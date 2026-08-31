import InfinityFirstLoad
import FiniteDoubleTerminal

/-! # The first weight-one load at infinity

This file starts the nonzero-transverse branch of the constant-core
infinity argument.  The first result is deliberately boundary-free: if the
weight-one load arrives before the quadratic normal scale, the normal part
of every Faber numerator is still too high.  The surviving pure load rows
would give a normalized exceptional `d`-orbit with zero normal vector, which
cannot meet its common cubic over an algebraically closed residue field.
-/

noncomputable section

open Polynomial

namespace GCD369CubeHahnRegular

/-- Every regular multiple of the square of a positive Hahn monomial has no
coefficient below twice the monomial exponent. -/
theorem coeff_monomial_sq_mul_eq_zero_of_lt
    {k : Type*} [Field k] (delta e : ℚ) (hdelta : 0 < delta)
    (he : e < 2 * delta) (x : GCD369CubeHahnRegular k) :
    (((monomial delta hdelta.le) ^ 2 * x).1).coeff e = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  change (↑e : WithTop ℚ) <
    (((HahnSeries.single delta (1 : k)) ^ 2 * x.1).orderTop)
  rw [HahnSeries.orderTop_mul, pow_two, HahnSeries.orderTop_mul,
    HahnSeries.orderTop_single one_ne_zero]
  have hx : (↑(0 : ℚ) : WithTop ℚ) ≤ x.1.orderTop := x.2
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr he) (by
    norm_num only [show (2 : ℚ) * delta = delta + delta by ring,
      WithTop.coe_add]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hx ((↑delta : WithTop ℚ) + ↑delta))

/-- A square of a positive Hahn monomial raises every regular factor to
order at least twice its exponent. -/
theorem orderTop_monomial_sq_mul_lower
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta)
    (x : GCD369CubeHahnRegular k) :
    (↑(2 * delta) : WithTop ℚ) ≤
      (((monomial delta hdelta.le) ^ 2 * x).1).orderTop := by
  change (↑(2 * delta) : WithTop ℚ) ≤
    (((HahnSeries.single delta (1 : k)) ^ 2 * x.1).orderTop)
  rw [pow_two, HahnSeries.orderTop_mul, HahnSeries.orderTop_mul,
    HahnSeries.orderTop_single one_ne_zero]
  have hx : (↑(0 : ℚ) : WithTop ℚ) ≤ x.1.orderTop := x.2
  norm_num only [show (2 : ℚ) * delta = delta + delta by ring,
    WithTop.coe_add]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hx ((↑delta : WithTop ℚ) + ↑delta)

/-- A positive Hahn monomial power raises every regular factor by at least
the corresponding multiple of its exponent. -/
theorem orderTop_monomial_pow_mul_lower
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta)
    (n : ℕ) (x : GCD369CubeHahnRegular k) :
    (↑((n : ℚ) * delta) : WithTop ℚ) ≤
      (((monomial delta hdelta.le) ^ n * x).1).orderTop := by
  change (↑((n : ℚ) * delta) : WithTop ℚ) ≤
    (((HahnSeries.single delta (1 : k)) ^ n * x.1).orderTop)
  rw [HahnSeries.single_pow, HahnSeries.orderTop_mul,
    HahnSeries.orderTop_single (by simp)]
  have hx : (↑(0 : ℚ) : WithTop ℚ) ≤ x.1.orderTop := x.2
  norm_num only [nsmul_eq_mul, one_pow, WithTop.coe_mul,
    WithTop.coe_natCast]
  simpa [add_comm] using
    add_le_add_left hx (↑((n : ℚ) * delta) : WithTop ℚ)

/-- If the regular factor has nonzero residue, the preceding lower bound is
exact. -/
theorem orderTop_monomial_pow_mul_eq_of_constantCoeff_ne
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta)
    (n : ℕ) (x : GCD369CubeHahnRegular k)
    (hx : constantCoeff x ≠ 0) :
    (((monomial delta hdelta.le) ^ n * x).1).orderTop =
      (↑((n : ℚ) * delta) : WithTop ℚ) := by
  have hxorder : x.1.orderTop = (↑(0 : ℚ) : WithTop ℚ) :=
    le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hx) x.2
  change (((HahnSeries.single delta (1 : k)) ^ n * x.1).orderTop) = _
  rw [HahnSeries.single_pow, HahnSeries.orderTop_mul,
    HahnSeries.orderTop_single (by simp), hxorder]
  norm_num only [nsmul_eq_mul, one_pow, WithTop.coe_mul,
    WithTop.coe_natCast]
  simp

/-- A monomial power strictly above a cutoff belongs to the corresponding
higher-order ideal. -/
theorem monomial_pow_mul_mem_higherOrderIdeal
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta)
    (n : ℕ) (x : GCD369CubeHahnRegular k) {e : ℚ}
    (he : 0 ≤ e) (hlt : e < (n : ℚ) * delta) :
    (monomial delta hdelta.le) ^ n * x ∈ higherOrderIdeal e he := by
  exact (WithTop.coe_lt_coe.mpr hlt).trans_le
    (orderTop_monomial_pow_mul_lower delta hdelta n x)

end GCD369CubeHahnRegular

/-- Every depressed cubic over an algebraically closed field has a root. -/
theorem GCD369CubeExistsDepressedCubicRoot
    {k : Type*} [Field k] [IsAlgClosed k] (u v : k) :
    ∃ r : k, r ^ 3 + u * r + v = 0 := by
  let P : k[X] := X ^ 3 + C u * X + C v
  have hdegree : P.degree ≠ 0 := by
    have hnat : P.natDegree = 3 := by
      dsimp only [P]
      compute_degree <;> norm_num
    rw [degree_eq_natDegree]
    · rw [hnat]
      norm_num
    · intro hzero
      have h := congrArg natDegree hzero
      simp [hnat] at h
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hdegree
  refine ⟨r, ?_⟩
  simpa [P, Polynomial.IsRoot] using hr

/-- The residual factor in the fifth pure-`d` numerator on the singular
common-cubic parametrization. -/
theorem GCD369CubeDTerminalResidual_doubleRoot
    {K : Type*} [CommRing K]
    (r : K) :
    540672 * (-3 * r ^ 2) ^ 5 * (2 * r ^ 3) -
        4055040 * (-3 * r ^ 2) ^ 2 * (2 * r ^ 3) ^ 3 =
      -554729472 * r ^ 13 := by
  ring

/-- At the balanced singular timing, the first, second, and fourth loaded
rows fix the fifth terminal residue.  The identity is polynomial, so it
does not require dividing by either projective coordinate. -/
theorem GCD369CubeDLoadBalancedTerminal_identity
    {K : Type*} [Field K] [CharZero K]
    (A r d q b T : K)
    (h1 :
      -23328 * (A ^ 2 * d - 2 * A * q - b) +
        798720 * r ^ 9 * T = 0)
    (h2 :
      -46656 * (2 * A ^ 2 * r * d - 3 * A * r * q +
        3 * r * b) - 2156544 * r ^ 10 * T = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * q - 65610 * r ^ 3 * b) -
        314928 * r * A ^ 3 + 26956800 * r ^ 12 * T = 0) :
    13 * (-2519424 * r ^ 2 * A ^ 3 - 554729472 * r ^ 13 * T) =
      -62985600 * r ^ 2 * A ^ 3 := by
  linear_combination
    (-3456 * r ^ 4) * h1 + (864 * r ^ 3) * h2 + (-96 * r) * h4

/-- Consequently the balanced fifth residue cannot vanish on a nonzero
singular projective jet. -/
theorem GCD369CubeDLoadBalancedTerminal_nonzero
    {K : Type*} [Field K] [CharZero K]
    (A r d q b T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -23328 * (A ^ 2 * d - 2 * A * q - b) +
        798720 * r ^ 9 * T = 0)
    (h2 :
      -46656 * (2 * A ^ 2 * r * d - 3 * A * r * q +
        3 * r * b) - 2156544 * r ^ 10 * T = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * q - 65610 * r ^ 3 * b) -
        314928 * r * A ^ 3 + 26956800 * r ^ 12 * T = 0) :
    -2519424 * r ^ 2 * A ^ 3 - 554729472 * r ^ 13 * T ≠ 0 := by
  intro hzero
  have hterminal := GCD369CubeDLoadBalancedTerminal_identity
    A r d q b T h1 h2 h4
  rw [hzero, mul_zero] at hterminal
  have hnonzero : (-62985600 : K) * r ^ 2 * A ^ 3 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
      (pow_ne_zero 3 hA)
  exact hnonzero hterminal.symm

/-- The weight-fourteen terminal polynomial on an arbitrary nonzero
weight-one `d` landing. -/
def GCD369CubeDExceptionalTerminalAt {K : Type*} [Field K]
    (Xn Yn Zn u v d : K) : K :=
  -729 * u ^ 3 * Xn ^ 2 + 2187 * v ^ 2 * Xn ^ 2 +
    4374 * u * v * Xn * Yn + 1458 * u ^ 2 * Xn * Zn +
    729 * u ^ 2 * Yn ^ 2 - 4374 * v * Yn * Zn +
    d * (320 * u ^ 5 * v - 2880 * u ^ 2 * v ^ 3)

/-- Arbitrary nonzero `d` rows retain the normalized terminal
nonvanishing certificate. -/
theorem GCD369CubeDExceptionalTerminalAt_nonzero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v d : K) (hd : d ≠ 0)
    (hrows : GCD369CubeDExceptionalRowsAt Xn Yn Zn u v d) :
    GCD369CubeDExceptionalTerminalAt Xn Yn Zn u v d ≠ 0 := by
  obtain ⟨lambda, hlambda, hscale, hnormalized⟩ :=
    GCD369CubeDExceptionalRowsAt_normalize hd hrows
  rcases hnormalized with ⟨hprojective, h1, h2, h3, h4⟩
  have horbit := GCD369CubeDExceptionalSupport
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v) h1 h2 h3 h4
  have hu := (GCD369CubeDExceptionalCoordinatesNonzero
    (lambda ^ 2 * u) (lambda ^ 3 * v) hprojective horbit).1
  have hterminal := GCD369CubeDExceptionalTerminalNonzero
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v) hu h1 h2 h4
  have hdvalue : d = lambda⁻¹ := by
    apply (mul_left_cancel₀ hlambda)
    rw [hscale]
    simp [hlambda]
  have hhomogeneous :
      GCD369CubeDExceptionalTerminalAt
        (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
        (lambda ^ 2 * u) (lambda ^ 3 * v) 1 =
      lambda ^ 14 * GCD369CubeDExceptionalTerminalAt Xn Yn Zn u v d := by
    rw [hdvalue]
    simp only [GCD369CubeDExceptionalTerminalAt]
    field_simp [hlambda]
  have hterminal' :
      GCD369CubeDExceptionalTerminalAt
        (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
        (lambda ^ 2 * u) (lambda ^ 3 * v) 1 ≠ 0 := by
    intro hzero
    apply hterminal
    dsimp only [GCD369CubeDExceptionalTerminalAt] at hzero
    linear_combination hzero
  intro hzero
  apply hterminal'
  rw [hhomogeneous, hzero, mul_zero]

/-- The common-cubic `u` coordinate cannot vanish on an arbitrary nonzero
`d` exceptional orbit. -/
theorem GCD369CubeDExceptionalRowsAt_u_ne_zero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v d : K) (hd : d ≠ 0)
    (hrows : GCD369CubeDExceptionalRowsAt Xn Yn Zn u v d) :
    u ≠ 0 := by
  obtain ⟨lambda, hlambda, _hscale, hnormalized⟩ :=
    GCD369CubeDExceptionalRowsAt_normalize hd hrows
  rcases hnormalized with ⟨hprojective, h1, h2, h3, h4⟩
  have horbit := GCD369CubeDExceptionalSupport
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v) h1 h2 h3 h4
  have hu := (GCD369CubeDExceptionalCoordinatesNonzero
    (lambda ^ 2 * u) (lambda ^ 3 * v) hprojective horbit).1
  intro hzero
  exact hu (by rw [hzero, mul_zero])

namespace GCD369CubeHahnCommonCoefficientData

/-- At the exact first-transverse tie, a weight-one ground-field load is
the square of the transverse monomial times its residue. -/
theorem TransverseScale.weightedRegular_one_constant_eq_transverse_sq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (htie : D.faber.scale.p = 2 * T.delta) :
    D.faber.scale.weightedRegular 1 D.faber.d =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant Kd := by
  rw [hd, D.faber.scale.weightedRegular_constant_eq_monomial_sq
    1 (by norm_num) Kd]
  apply Subtype.ext
  change
    (HahnSeries.single (((1 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
        HahnSeries.C Kd =
      (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C Kd
  rw [htie]
  congr 4 <;> ring

/-- The first zero-high numerator has no coefficient below the quadratic
normal scale. -/
theorem TransverseScale.zeroHighN1Coeff_zero_of_lt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    {e : ℚ} (he : e < 2 * T.delta) :
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff e = 0 := by
  rw [T.zeroHighN1Expansion]
  let A : GCD369CubeHahnRegular k :=
    -32 * GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU
  change (A * (monomial T.delta T.hdelta.le) ^ 2).1.coeff e = 0
  rw [mul_comm, monomial_eq_regularMonomial]
  exact GCD369CubeHahnRegular.coeff_monomial_sq_mul_eq_zero_of_lt
    T.delta e T.hdelta he A

/-- The second zero-high numerator has no coefficient below the quadratic
normal scale. -/
theorem TransverseScale.zeroHighN2Coeff_zero_of_lt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    {e : ℚ} (he : e < 2 * T.delta) :
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff e = 0 := by
  rw [T.zeroHighN2Expansion]
  let A : GCD369CubeHahnRegular k :=
    32 * GCD369CubeNormalRow2 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  change (A * (monomial T.delta T.hdelta.le) ^ 2).1.coeff e = 0
  rw [mul_comm, monomial_eq_regularMonomial]
  exact GCD369CubeHahnRegular.coeff_monomial_sq_mul_eq_zero_of_lt
    T.delta e T.hdelta he A

/-- The fourth zero-high numerator has no coefficient below the quadratic
normal scale.  Its cubic correction is absorbed into the remaining regular
factor. -/
theorem TransverseScale.zeroHighN4Coeff_zero_of_lt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    {e : ℚ} (he : e < 2 * T.delta) :
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff e = 0 := by
  rw [T.zeroHighN4Expansion]
  let H : GCD369CubeHahnRegular k := monomial T.delta T.hdelta.le
  let A : GCD369CubeHahnRegular k :=
    32 * GCD369CubeNormalRow4 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let B : GCD369CubeHahnRegular k := 314928 * T.Yn * T.Xn ^ 2
  have hfactor : A * H ^ 2 - B * H ^ 3 =
      H ^ 2 * (A - B * H) := by ring
  rw [hfactor]
  dsimp only [H]
  rw [monomial_eq_regularMonomial]
  exact GCD369CubeHahnRegular.coeff_monomial_sq_mul_eq_zero_of_lt
    T.delta e T.hdelta he (A - B * H)

/-- A nonzero constant `d` cannot arrive strictly before the first
quadratic transverse correction.  Unlike the finite-place theorem, this
uses no original-value boundary packet. -/
theorem TransverseScale.d_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant Kc7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant Kc5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant Kc4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant Kc3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant Kc2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant Kc1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Kr1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Kr2)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Kr4)
    (hbefore : D.faber.scale.p < 2 * T.delta) :
    Kd = 0 := by
  let F := D.faber
  let P1 : GCD369CubeHahnRegular k :=
    27648 * F.scale.regular0 * F.scale.regular3 +
      27648 * F.scale.regular1 * F.scale.regular2 -
      9216 * F.scale.regular1 * F.scale.regular4 ^ 2 -
      18432 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 -
      3072 * F.scale.regular3 ^ 3 +
      5120 * F.scale.regular3 * F.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    82944 * F.scale.regular0 * F.scale.regular2 -
      27648 * F.scale.regular0 * F.scale.regular4 ^ 2 +
      41472 * F.scale.regular1 ^ 2 -
      55296 * F.scale.regular1 * F.scale.regular3 * F.scale.regular4 -
      27648 * F.scale.regular2 ^ 2 * F.scale.regular4 -
      27648 * F.scale.regular2 * F.scale.regular3 ^ 2 +
      15360 * F.scale.regular2 * F.scale.regular4 ^ 3 +
      23040 * F.scale.regular3 ^ 2 * F.scale.regular4 ^ 2 -
      2048 * F.scale.regular4 ^ 5
  let P4 : GCD369CubeHahnRegular k :=
    373248 * F.scale.regular0 ^ 2 -
      248832 * F.scale.regular0 * F.scale.regular2 * F.scale.regular4 -
      124416 * F.scale.regular0 * F.scale.regular3 ^ 2 +
      55296 * F.scale.regular0 * F.scale.regular4 ^ 3 -
      124416 * F.scale.regular1 ^ 2 * F.scale.regular4 -
      373248 * F.scale.regular1 * F.scale.regular2 * F.scale.regular3 +
      207360 * F.scale.regular1 * F.scale.regular3 * F.scale.regular4 ^ 2 -
      82944 * F.scale.regular2 ^ 3 +
      124416 * F.scale.regular2 ^ 2 * F.scale.regular4 ^ 2 +
      248832 * F.scale.regular2 * F.scale.regular3 ^ 2 * F.scale.regular4 -
      46080 * F.scale.regular2 * F.scale.regular4 ^ 4 +
      20736 * F.scale.regular3 ^ 4 -
      92160 * F.scale.regular3 ^ 2 * F.scale.regular4 ^ 3 +
      5120 * F.scale.regular4 ^ 6
  have hz1 := F.dN1Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1
    hc7 hc5 hc4 hc3 hc2 hc1 hr1
  have hz2 := F.dN2Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr2
    hc7 hc5 hc4 hc3 hc2 hc1 hr2
  have hz4 := F.dN4Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr4
    hc7 hc5 hc4 hc3 hc2 hc1 hr4
  have hzero1 := T.zeroHighN1Coeff_zero_of_lt hbefore
  have hzero2 := T.zeroHighN2Coeff_zero_of_lt hbefore
  have hzero4 := T.zeroHighN4Coeff_zero_of_lt hbefore
  have hpHalf : 0 < F.scale.p / 2 :=
    div_pos F.scale.hp (by norm_num)
  have hweighted :
      F.scale.weightedRegular 1 F.d =
        GCD369CubeHahnRegular.monomial
            (F.scale.p / 2) hpHalf.le ^ 2 *
          GCD369CubeHahnRegular.constant Kd := by
    rw [hd]
    simpa using F.scale.weightedRegular_constant_eq_monomial_sq
      1 (by norm_num) Kd
  have hload1 :
      ((GCD369CubeHahnRegular.monomial
          (F.scale.p / 2) hpHalf.le) ^ 2 *
        GCD369CubeHahnRegular.constant Kd * P1).1.coeff F.scale.p =
          Kd * GCD369CubeHahnRegular.constantCoeff P1 := by
    convert GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      (F.scale.p / 2) hpHalf Kd P1 using 1 <;> ring
  have hload2 :
      ((GCD369CubeHahnRegular.monomial
          (F.scale.p / 2) hpHalf.le) ^ 2 *
        GCD369CubeHahnRegular.constant Kd * P2).1.coeff F.scale.p =
          Kd * GCD369CubeHahnRegular.constantCoeff P2 := by
    convert GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      (F.scale.p / 2) hpHalf Kd P2 using 1 <;> ring
  have hload4 :
      ((GCD369CubeHahnRegular.monomial
          (F.scale.p / 2) hpHalf.le) ^ 2 *
        GCD369CubeHahnRegular.constant Kd * P4).1.coeff F.scale.p =
          Kd * GCD369CubeHahnRegular.constantCoeff P4 := by
    convert GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      (F.scale.p / 2) hpHalf Kd P4 using 1 <;> ring
  change
    (729 * GCD369CubeFaberN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P1).1.coeff F.scale.p = 0 at hz1
  change
    (2187 * GCD369CubeFaberN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P2).1.coeff F.scale.p = 0 at hz2
  change
    (6561 * GCD369CubeFaberN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P4).1.coeff F.scale.p = 0 at hz4
  rw [hzero1, hweighted, hload1, zero_add] at hz1
  rw [hzero2, hweighted, hload2, zero_add] at hz2
  rw [hzero4, hweighted, hload4, zero_add] at hz4
  simp only [P1, P2, P4, map_add, map_sub, map_mul, map_pow,
    map_ofNat] at hz1 hz2 hz4
  change Kd *
    (27648 * F.scale.leading0 * F.scale.leading3 +
      27648 * F.scale.leading1 * F.scale.leading2 -
      9216 * F.scale.leading1 * F.scale.leading4 ^ 2 -
      18432 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 -
      3072 * F.scale.leading3 ^ 3 +
      5120 * F.scale.leading3 * F.scale.leading4 ^ 3) = 0 at hz1
  change Kd *
    (82944 * F.scale.leading0 * F.scale.leading2 -
      27648 * F.scale.leading0 * F.scale.leading4 ^ 2 +
      41472 * F.scale.leading1 ^ 2 -
      55296 * F.scale.leading1 * F.scale.leading3 * F.scale.leading4 -
      27648 * F.scale.leading2 ^ 2 * F.scale.leading4 -
      27648 * F.scale.leading2 * F.scale.leading3 ^ 2 +
      15360 * F.scale.leading2 * F.scale.leading4 ^ 3 +
      23040 * F.scale.leading3 ^ 2 * F.scale.leading4 ^ 2 -
      2048 * F.scale.leading4 ^ 5) = 0 at hz2
  change Kd *
    (373248 * F.scale.leading0 ^ 2 -
      248832 * F.scale.leading0 * F.scale.leading2 * F.scale.leading4 -
      124416 * F.scale.leading0 * F.scale.leading3 ^ 2 +
      55296 * F.scale.leading0 * F.scale.leading4 ^ 3 -
      124416 * F.scale.leading1 ^ 2 * F.scale.leading4 -
      373248 * F.scale.leading1 * F.scale.leading2 * F.scale.leading3 +
      207360 * F.scale.leading1 * F.scale.leading3 * F.scale.leading4 ^ 2 -
      82944 * F.scale.leading2 ^ 3 +
      124416 * F.scale.leading2 ^ 2 * F.scale.leading4 ^ 2 +
      248832 * F.scale.leading2 * F.scale.leading3 ^ 2 * F.scale.leading4 -
      46080 * F.scale.leading2 * F.scale.leading4 ^ 4 +
      20736 * F.scale.leading3 ^ 4 -
      92160 * F.scale.leading3 ^ 2 * F.scale.leading4 ^ 3 +
      5120 * F.scale.leading4 ^ 6) = 0 at hz4
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4] at hz1 hz2 hz4
  by_contra hKd
  have hrow1 :
      320 * Kd * D.u ^ 3 * D.v - 960 * Kd * D.v ^ 3 = 0 := by
    linear_combination (-1 / 32) * hz1
  have hrow2 :
      64 * Kd * D.u ^ 5 - 1440 * Kd * D.u ^ 2 * D.v ^ 2 = 0 := by
    linear_combination (1 / 32) * hz2
  have hrow4 :
      160 * Kd * D.u ^ 6 - 5760 * Kd * D.u ^ 3 * D.v ^ 2 +
        6480 * Kd * D.v ^ 4 = 0 := by
    linear_combination (1 / 32) * hz4
  have hrowsAt :
      GCD369CubeDExceptionalRowsAt 0 0 0 D.u D.v Kd := by
    refine ⟨D.hprojective, ?_, ?_, ?_, ?_⟩
    · simpa [GCD369CubeNormalRow1] using hrow1
    · simpa [GCD369CubeNormalRow2] using hrow2
    · simp [GCD369CubeNormalRow3]
    · simpa [GCD369CubeNormalRow4] using hrow4
  obtain ⟨lambda, hlambda, _hscale, hrows⟩ :=
    GCD369CubeDExceptionalRowsAt_normalize hKd hrowsAt
  have hrows' : GCD369CubeDExceptionalRows
      0 0 0 (lambda ^ 2 * D.u) (lambda ^ 3 * D.v) := by
    simpa only [mul_zero] using hrows
  have hnocommon := (GCD369CubeEarlyLoadRows.d hrows').noCommonRoot
  obtain ⟨r, hr⟩ := GCD369CubeExistsDepressedCubicRoot
    (lambda ^ 2 * D.u) (lambda ^ 3 * D.v)
  exact hnocommon r hr (by ring)

set_option maxHeartbeats 1000000 in
/-- At the exact tie `p = 2*delta`, the four source coefficients are the
arbitrary-`d` exceptional row packet on the first transverse residue. -/
theorem TransverseScale.dExceptionalRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant Kc7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant Kc5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant Kc4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant Kc3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant Kc2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant Kc1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Kr1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Kr2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Kr3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Kr4)
    (htie : D.faber.scale.p = 2 * T.delta) :
    GCD369CubeDExceptionalRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v Kd := by
  let F := D.faber
  let q : ℚ := ((1 : ℕ) : ℚ) * F.scale.p / 2
  have hq : 0 < q := by
    dsimp only [q]
    exact div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num)
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial q hq.le
  let P1 : GCD369CubeHahnRegular k :=
    27648 * F.scale.regular0 * F.scale.regular3 +
      27648 * F.scale.regular1 * F.scale.regular2 -
      9216 * F.scale.regular1 * F.scale.regular4 ^ 2 -
      18432 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 -
      3072 * F.scale.regular3 ^ 3 +
      5120 * F.scale.regular3 * F.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    82944 * F.scale.regular0 * F.scale.regular2 -
      27648 * F.scale.regular0 * F.scale.regular4 ^ 2 +
      41472 * F.scale.regular1 ^ 2 -
      55296 * F.scale.regular1 * F.scale.regular3 * F.scale.regular4 -
      27648 * F.scale.regular2 ^ 2 * F.scale.regular4 -
      27648 * F.scale.regular2 * F.scale.regular3 ^ 2 +
      15360 * F.scale.regular2 * F.scale.regular4 ^ 3 +
      23040 * F.scale.regular3 ^ 2 * F.scale.regular4 ^ 2 -
      2048 * F.scale.regular4 ^ 5
  let P3 : GCD369CubeHahnRegular k :=
    110592 * F.scale.regular0 * F.scale.regular1 -
      55296 * F.scale.regular0 * F.scale.regular3 * F.scale.regular4 -
      55296 * F.scale.regular1 * F.scale.regular2 * F.scale.regular4 -
      36864 * F.scale.regular1 * F.scale.regular3 ^ 2 +
      14336 * F.scale.regular1 * F.scale.regular4 ^ 3 -
      36864 * F.scale.regular2 ^ 2 * F.scale.regular3 +
      49152 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 ^ 2 +
      18432 * F.scale.regular3 ^ 3 * F.scale.regular4 -
      10240 * F.scale.regular3 * F.scale.regular4 ^ 4
  let P4 : GCD369CubeHahnRegular k :=
    373248 * F.scale.regular0 ^ 2 -
      248832 * F.scale.regular0 * F.scale.regular2 * F.scale.regular4 -
      124416 * F.scale.regular0 * F.scale.regular3 ^ 2 +
      55296 * F.scale.regular0 * F.scale.regular4 ^ 3 -
      124416 * F.scale.regular1 ^ 2 * F.scale.regular4 -
      373248 * F.scale.regular1 * F.scale.regular2 * F.scale.regular3 +
      207360 * F.scale.regular1 * F.scale.regular3 * F.scale.regular4 ^ 2 -
      82944 * F.scale.regular2 ^ 3 +
      124416 * F.scale.regular2 ^ 2 * F.scale.regular4 ^ 2 +
      248832 * F.scale.regular2 * F.scale.regular3 ^ 2 * F.scale.regular4 -
      46080 * F.scale.regular2 * F.scale.regular4 ^ 4 +
      20736 * F.scale.regular3 ^ 4 -
      92160 * F.scale.regular3 ^ 2 * F.scale.regular4 ^ 3 +
      5120 * F.scale.regular4 ^ 6
  have hz1 := F.dN1Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1
    hc7 hc5 hc4 hc3 hc2 hc1 hr1
  have hz2 := F.dN2Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr2
    hc7 hc5 hc4 hc3 hc2 hc1 hr2
  have hz3 := F.dN3Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr3
    hc7 hc5 hc4 hc3 hc2 hc1 hr3
  have hz4 := F.dN4Coeff_zero Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr4
    hc7 hc5 hc4 hc3 hc2 hc1 hr4
  have hweighted : F.scale.weightedRegular 1 F.d =
      H ^ 2 * GCD369CubeHahnRegular.constant Kd := by
    rw [hd, F.scale.weightedRegular_constant_eq_monomial_sq
      1 (by norm_num) Kd]
  have hload (P : GCD369CubeHahnRegular k) :
      (H ^ 2 * GCD369CubeHahnRegular.constant Kd * P).1.coeff
          F.scale.p =
        Kd * GCD369CubeHahnRegular.constantCoeff P := by
    dsimp only [H]
    convert GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      q hq Kd P using 1 <;> dsimp only [q] <;> ring
  have hzero1 := T.zeroHighN1Coeff
  have hzero2 := T.zeroHighN2Coeff
  have hzero3 := T.zeroHighN3Coeff
  have hzero4 := T.zeroHighN4Coeff
  change
    (729 * GCD369CubeFaberN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff (2 * T.delta) = _ at hzero1
  change
    (2187 * GCD369CubeFaberN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff (2 * T.delta) = _ at hzero2
  change
    (GCD369CubeFaberN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff (2 * T.delta) = _ at hzero3
  change
    (6561 * GCD369CubeFaberN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff (2 * T.delta) = _ at hzero4
  change
    (729 * GCD369CubeFaberN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P1).1.coeff F.scale.p = 0 at hz1
  change
    (2187 * GCD369CubeFaberN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P2).1.coeff F.scale.p = 0 at hz2
  change
    (243 * GCD369CubeFaberN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P3).1.coeff F.scale.p = 0 at hz3
  change
    (6561 * GCD369CubeFaberN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff F.scale.p +
      (F.scale.weightedRegular 1 F.d * P4).1.coeff F.scale.p = 0 at hz4
  rw [hweighted, hload, htie, hzero1] at hz1
  rw [hweighted, hload, htie, hzero2] at hz2
  have hzero3' :
      (243 * GCD369CubeFaberN3
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4).1.coeff (2 * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
    calc
      _ = (243 : k) *
          (GCD369CubeFaberN3
            F.scale.regular0 F.scale.regular1 F.scale.regular2
            F.scale.regular3 F.scale.regular4).1.coeff (2 * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
      _ = _ := by rw [hzero3]; ring
  rw [hweighted, hload, htie, hzero3'] at hz3
  rw [hweighted, hload, htie, hzero4] at hz4
  simp only [P1, P2, P3, P4, map_add, map_sub, map_mul, map_pow,
    map_ofNat] at hz1 hz2 hz3 hz4
  change _ + Kd *
    (27648 * F.scale.leading0 * F.scale.leading3 +
      27648 * F.scale.leading1 * F.scale.leading2 -
      9216 * F.scale.leading1 * F.scale.leading4 ^ 2 -
      18432 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 -
      3072 * F.scale.leading3 ^ 3 +
      5120 * F.scale.leading3 * F.scale.leading4 ^ 3) = 0 at hz1
  change _ + Kd *
    (82944 * F.scale.leading0 * F.scale.leading2 -
      27648 * F.scale.leading0 * F.scale.leading4 ^ 2 +
      41472 * F.scale.leading1 ^ 2 -
      55296 * F.scale.leading1 * F.scale.leading3 * F.scale.leading4 -
      27648 * F.scale.leading2 ^ 2 * F.scale.leading4 -
      27648 * F.scale.leading2 * F.scale.leading3 ^ 2 +
      15360 * F.scale.leading2 * F.scale.leading4 ^ 3 +
      23040 * F.scale.leading3 ^ 2 * F.scale.leading4 ^ 2 -
      2048 * F.scale.leading4 ^ 5) = 0 at hz2
  change _ + Kd *
    (110592 * F.scale.leading0 * F.scale.leading1 -
      55296 * F.scale.leading0 * F.scale.leading3 * F.scale.leading4 -
      55296 * F.scale.leading1 * F.scale.leading2 * F.scale.leading4 -
      36864 * F.scale.leading1 * F.scale.leading3 ^ 2 +
      14336 * F.scale.leading1 * F.scale.leading4 ^ 3 -
      36864 * F.scale.leading2 ^ 2 * F.scale.leading3 +
      49152 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 ^ 2 +
      18432 * F.scale.leading3 ^ 3 * F.scale.leading4 -
      10240 * F.scale.leading3 * F.scale.leading4 ^ 4) = 0 at hz3
  change _ + Kd *
    (373248 * F.scale.leading0 ^ 2 -
      248832 * F.scale.leading0 * F.scale.leading2 * F.scale.leading4 -
      124416 * F.scale.leading0 * F.scale.leading3 ^ 2 +
      55296 * F.scale.leading0 * F.scale.leading4 ^ 3 -
      124416 * F.scale.leading1 ^ 2 * F.scale.leading4 -
      373248 * F.scale.leading1 * F.scale.leading2 * F.scale.leading3 +
      207360 * F.scale.leading1 * F.scale.leading3 * F.scale.leading4 ^ 2 -
      82944 * F.scale.leading2 ^ 3 +
      124416 * F.scale.leading2 ^ 2 * F.scale.leading4 ^ 2 +
      248832 * F.scale.leading2 * F.scale.leading3 ^ 2 * F.scale.leading4 -
      46080 * F.scale.leading2 * F.scale.leading4 ^ 4 +
      20736 * F.scale.leading3 ^ 4 -
      92160 * F.scale.leading3 ^ 2 * F.scale.leading4 ^ 3 +
      5120 * F.scale.leading4 ^ 6) = 0 at hz4
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4] at hz1 hz2 hz3 hz4
  refine ⟨D.hprojective, ?_, ?_, ?_, ?_⟩
  · linear_combination (-1 / 32) * hz1
  · linear_combination (1 / 32) * hz2
  · linear_combination (1 / 31104) * hz3
  · linear_combination (1 / 32) * hz4

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Along the exact common-cubic chart, the pure-`d` fifth numerator is a
fixed combination of the first two loaded rows, the intrinsic cubic, and
one regular residual factor.  The displayed residue is the only part of
that factor which can occur at the active `d` exponent. -/
theorem TransverseScale.dTerminalRelation
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    let H : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let dload := D.faber.scale.weightedRegular 1 D.faber.d
    ∃ Rem : GCD369CubeHahnRegular k,
      GCD369CubeHahnRegular.constantCoeff Rem =
        540672 * D.u ^ 5 * D.v - 4055040 * D.u ^ 2 * D.v ^ 3 ∧
      GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 dload 0 0 0 0 0 0 =
        24 * D.cubicU ^ 2 *
            GCD369CubeFaberD1
              D.faber.scale.regular0 D.faber.scale.regular1
              D.faber.scale.regular2 D.faber.scale.regular3
              D.faber.scale.regular4 dload -
          24 * D.cubicV *
            GCD369CubeFaberD2
              D.faber.scale.regular0 D.faber.scale.regular1
              D.faber.scale.regular2 D.faber.scale.regular3
              D.faber.scale.regular4 dload +
          839808 * H ^ 3 *
            GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU +
          dload * Rem := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let dload := D.faber.scale.weightedRegular 1 D.faber.d
  let P1 : GCD369CubeHahnRegular k :=
    27648 * D.faber.scale.regular0 * D.faber.scale.regular3 +
      27648 * D.faber.scale.regular1 * D.faber.scale.regular2 -
      9216 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 2 -
      18432 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      3072 * D.faber.scale.regular3 ^ 3 +
      5120 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    82944 * D.faber.scale.regular0 * D.faber.scale.regular2 -
      27648 * D.faber.scale.regular0 * D.faber.scale.regular4 ^ 2 +
      41472 * D.faber.scale.regular1 ^ 2 -
      55296 * D.faber.scale.regular1 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      27648 * D.faber.scale.regular2 ^ 2 * D.faber.scale.regular4 -
      27648 * D.faber.scale.regular2 * D.faber.scale.regular3 ^ 2 +
      15360 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 3 +
      23040 * D.faber.scale.regular3 ^ 2 *
        D.faber.scale.regular4 ^ 2 -
      2048 * D.faber.scale.regular4 ^ 5
  let Rem : GCD369CubeHahnRegular k :=
    GCD369CubeFaberFullN5_dCoeff
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 -
    24 * D.cubicU ^ 2 * P1 + 24 * D.cubicV * P2
  refine ⟨Rem, ?_, ?_⟩
  · dsimp only [Rem, P1, P2, GCD369CubeFaberFullN5_dCoeff]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      D.constantCoeff_cubicU, D.constantCoeff_cubicV]
    have ha0 : GCD369CubeHahnRegular.constantCoeff
        D.faber.scale.regular0 = D.faber.scale.leading0 := rfl
    have ha1 : GCD369CubeHahnRegular.constantCoeff
        D.faber.scale.regular1 = D.faber.scale.leading1 := rfl
    have ha2 : GCD369CubeHahnRegular.constantCoeff
        D.faber.scale.regular2 = D.faber.scale.leading2 := rfl
    have ha3 : GCD369CubeHahnRegular.constantCoeff
        D.faber.scale.regular3 = D.faber.scale.leading3 := rfl
    have ha4 : GCD369CubeHahnRegular.constantCoeff
        D.faber.scale.regular4 = D.faber.scale.leading4 := rfl
    rw [ha0, ha1, ha2, ha3, ha4]
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
    ring
  · have h1 := T.zeroHighN1Expansion
    have h2 := T.zeroHighN2Expansion
    have h5 := GCD369CubeFaberFullN5_zeroHigh_expansion
      T.Xn T.Yn T.Zn D.cubicU D.cubicV H
    have hchart0 : D.faber.scale.regular0 =
        D.cubicV ^ 2 + H * T.Zn := by
      rw [T.regular0_eq]
      dsimp only [H]
      rw [monomial_eq_regularMonomial]
      ring
    have hchart1 : D.faber.scale.regular1 =
        2 * D.cubicU * D.cubicV + H * T.Yn := by
      rw [T.regular1_eq]
      dsimp only [H]
      rw [monomial_eq_regularMonomial]
      ring
    have hchart2 : D.faber.scale.regular2 =
        D.cubicU ^ 2 + H * T.Xn := by
      rw [T.regular2_eq]
      dsimp only [H]
      rw [monomial_eq_regularMonomial]
      ring
    have hzero5 :
        GCD369CubeFaberFullN5
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 0 0 0 0 0 0 0 =
        559872 * H ^ 2 *
            GCD369CubeNormalRow5 T.Xn T.Yn T.Zn
              D.cubicU D.cubicV +
          839808 * H ^ 3 *
            GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU := by
      rw [hchart0, hchart1, hchart2,
        D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
      exact h5
    rw [GCD369CubeFaberFullN5_d_specialize, hzero5]
    dsimp only [GCD369CubeFaberD1, GCD369CubeFaberD2, dload, Rem]
    rw [h1, h2]
    rw [monomial_eq_regularMonomial]
    dsimp only [H]
    have hrow5 := GCD369CubeNormalRow5_of_row1_row2
      T.Xn T.Yn T.Zn D.cubicU D.cubicV
    linear_combination (768 * H ^ 2) * hrow5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exact divisibility of the specialized fifth numerator by the square of
the first transverse monomial; the displayed factor is its residue. -/
theorem TransverseScale.dTerminalFactor_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (htie : D.faber.scale.p = 2 * T.delta) :
    let H : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let K : GCD369CubeHahnRegular k :=
      559872 * GCD369CubeNormalRow5 T.Xn T.Yn T.Zn D.cubicU D.cubicV +
        245760 * D.cubicU ^ 2 * D.cubicV *
          (D.cubicU ^ 3 - 9 * D.cubicV ^ 2) *
            GCD369CubeHahnRegular.constant Kd
    ∃ E : GCD369CubeHahnRegular k,
      GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        0 0 0 0 0 0 = H ^ 2 * K + H ^ 3 * E := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU +
      73728 *
        (2 * D.cubicU ^ 4 * T.Yn +
          5 * D.cubicU ^ 3 * D.cubicV * T.Xn -
          27 * D.cubicU * D.cubicV ^ 2 * T.Yn +
          9 * D.cubicV ^ 3 * T.Xn -
          18 * D.cubicU ^ 2 * D.cubicV * T.Zn) *
            GCD369CubeHahnRegular.constant Kd +
      H * (331776 *
        (5 * D.cubicU ^ 2 * T.Xn * T.Yn +
          6 * D.cubicU * D.cubicV * T.Xn ^ 2 -
          6 * D.cubicU * T.Yn * T.Zn -
          6 * D.cubicV * T.Yn ^ 2 -
          6 * D.cubicV * T.Xn * T.Zn) *
            GCD369CubeHahnRegular.constant Kd) -
      H ^ 2 * (995328 * T.Xn ^ 2 * T.Yn *
        GCD369CubeHahnRegular.constant Kd)
  refine ⟨E, ?_⟩
  have hload := T.weightedRegular_one_constant_eq_transverse_sq
    Kd hd htie
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU, hload]
  have hH : monomial T.delta T.hdelta.le = H := by
    exact (monomial_eq_regularMonomial T.delta T.hdelta.le).trans rfl
  rw [hH]
  have ha0 : D.cubicV ^ 2 + T.Zn * H =
      D.cubicV ^ 2 + H * T.Zn := by ring
  have ha1 : 2 * D.cubicU * D.cubicV + T.Yn * H =
      2 * D.cubicU * D.cubicV + H * T.Yn := by ring
  have ha2 : D.cubicU ^ 2 + T.Xn * H =
      D.cubicU ^ 2 + H * T.Xn := by ring
  rw [ha0, ha1, ha2, GCD369CubeFaberFullN5_d_expansion]
  dsimp only [H, E]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the exact tie, the specialized fifth numerator has coefficient
`768` times the arbitrary-`d` exceptional terminal polynomial. -/
theorem TransverseScale.dTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (htie : D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      0 0 0 0 0 0).1.coeff D.faber.scale.p =
      768 * GCD369CubeDExceptionalTerminalAt
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn)
        D.u D.v Kd := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5 T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      245760 * D.cubicU ^ 2 * D.cubicV *
        (D.cubicU ^ 3 - 9 * D.cubicV ^ 2) *
          GCD369CubeHahnRegular.constant Kd
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU +
      73728 *
        (2 * D.cubicU ^ 4 * T.Yn +
          5 * D.cubicU ^ 3 * D.cubicV * T.Xn -
          27 * D.cubicU * D.cubicV ^ 2 * T.Yn +
          9 * D.cubicV ^ 3 * T.Xn -
          18 * D.cubicU ^ 2 * D.cubicV * T.Zn) *
            GCD369CubeHahnRegular.constant Kd +
      H * (331776 *
        (5 * D.cubicU ^ 2 * T.Xn * T.Yn +
          6 * D.cubicU * D.cubicV * T.Xn ^ 2 -
          6 * D.cubicU * T.Yn * T.Zn -
          6 * D.cubicV * T.Yn ^ 2 -
          6 * D.cubicV * T.Xn * T.Zn) *
            GCD369CubeHahnRegular.constant Kd) -
      H ^ 2 * (995328 * T.Xn ^ 2 * T.Yn *
        GCD369CubeHahnRegular.constant Kd)
  have hload := T.weightedRegular_one_constant_eq_transverse_sq
    Kd hd htie
  have hfactor :
      GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        0 0 0 0 0 0 = H ^ 2 * K + H ^ 3 * E := by
    rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU, hload]
    have hH : monomial T.delta T.hdelta.le = H := by
      exact (monomial_eq_regularMonomial T.delta T.hdelta.le).trans rfl
    rw [hH]
    have ha0 : D.cubicV ^ 2 + T.Zn * H =
        D.cubicV ^ 2 + H * T.Zn := by ring
    have ha1 : 2 * D.cubicU * D.cubicV + T.Yn * H =
        2 * D.cubicU * D.cubicV + H * T.Yn := by ring
    have ha2 : D.cubicU ^ 2 + T.Xn * H =
        D.cubicU ^ 2 + H * T.Xn := by ring
    rw [ha0, ha1, ha2, GCD369CubeFaberFullN5_d_expansion]
    dsimp only [H, K, E]
    ring
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta)) hfactor
  have hmain := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 2 K
  have hhigh := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
    T.delta T.hdelta 2 3 (by norm_num) E
  change (H ^ 2 * K).1.coeff (2 * T.delta) =
    GCD369CubeHahnRegular.constantCoeff K at hmain
  change (H ^ 3 * E).1.coeff (2 * T.delta) = 0 at hhigh
  change
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      0 0 0 0 0 0).1.coeff (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [htie]
  rw [hc]
  dsimp only [K]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    D.constantCoeff_cubicU, D.constantCoeff_cubicV,
    GCD369CubeNormalRow5_map,
    GCD369CubeHahnRegular.constantCoeff_constant]
  dsimp only [GCD369CubeDExceptionalTerminalAt, GCD369CubeNormalRow5]
  ring

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnFaberPoleData

/-- The first two pure-`d` source rows vanish strictly beyond the active
weight-one exponent.  This is the order-theoretic strengthening of the two
coefficient lemmas used by the terminal relation. -/
theorem dN12_mem_higherOrderIdeal
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 R1 R2 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2) :
    GCD369CubeFaberD1
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4
        (F.scale.weightedRegular 1 F.d) ∈
          GCD369CubeHahnRegular.higherOrderIdeal
            F.scale.p F.scale.hp.le ∧
    GCD369CubeFaberD2
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4
        (F.scale.weightedRegular 1 F.d) ∈
          GCD369CubeHahnRegular.higherOrderIdeal
            F.scale.p F.scale.hp.le := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal F.scale.p F.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 < w) :
      F.scale.p < (w : ℚ) * F.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 F.scale.hp.le (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 F.scale.hp.le (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 F.scale.hp.le (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 F.scale.hp.le (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 F.scale.hp.le (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 F.scale.hp.le (hweight 8 (by norm_num))
  have hr1q : q (F.scale.weightedRegular 10 F.rho1) = 0 := by
    rw [hr1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 10 R1 F.scale.hp.le (hweight 10 (by norm_num))
  have hr2q : q (F.scale.weightedRegular 11 F.rho2) = 0 := by
    rw [hr2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 11 R2 F.scale.hp.le (hweight 11 (by norm_num))
  let full1 := GCD369CubeFaberFullN1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let full2 := GCD369CubeFaberFullN2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow1 := GCD369CubeFaberD1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
  let drow2 := GCD369CubeFaberD2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
  have hq1 : q full1 = q drow1 := by
    dsimp only [full1, drow1]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).1,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ _).1
  have hq2 : q full2 = q drow2 := by
    dsimp only [full2, drow2]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).2.1,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ _).2.1
  have hfull1 : full1 = 62208 * F.scale.weightedRegular 10 F.rho1 := by
    apply Subtype.ext
    exact F.scaledFullN1
  have hfull2 : full2 = 186624 * F.scale.weightedRegular 11 F.rho2 := by
    apply Subtype.ext
    exact F.scaledFullN2
  have hqfull1 : q full1 = 0 := by
    rw [hfull1, map_mul, hr1q, mul_zero]
  have hqfull2 : q full2 = 0 := by
    rw [hfull2, map_mul, hr2q, mul_zero]
  constructor
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hq1 ▸ hqfull1
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hq2 ▸ hqfull2

/-- The difference between the full fifth numerator and its pure `d`
specialization is strictly beyond the weight-one exponent. -/
theorem fullN5_sub_dSpecialized_mem_higherOrderIdeal
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1) :
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1) -
    (GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      0 0 0 0 0 0) ∈
        GCD369CubeHahnRegular.higherOrderIdeal
          F.scale.p F.scale.hp.le := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal F.scale.p F.scale.hp.le
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 1 < w) :
      F.scale.p < (w : ℚ) * F.scale.p := by
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right
        (show (1 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 F.scale.hp.le (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 F.scale.hp.le (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 F.scale.hp.le (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 F.scale.hp.le (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 F.scale.hp.le (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 F.scale.hp.le (hweight 8 (by norm_num))
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d) 0 0 0 0 0 0
  have hq : q full = q drow := by
    dsimp only [full, drow]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    simp
  have hdiff_mem : full - drow ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, hq, sub_self]
  exact hdiff_mem

/-- Through the weight-one exponent, every later constant load is invisible
in the fifth numerator. -/
theorem fullN5Coeff_eq_dSpecialized
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C7 C5 C4 C3 C2 C1 : k)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1) :
    (GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1)).1.coeff F.scale.p =
    (GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      0 0 0 0 0 0).1.coeff F.scale.p := by
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let drow : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d) 0 0 0 0 0 0
  have hdiff_mem : full - drow ∈
      GCD369CubeHahnRegular.higherOrderIdeal
        F.scale.p F.scale.hp.le :=
    F.fullN5_sub_dSpecialized_mem_higherOrderIdeal
      C7 C5 C4 C3 C2 C1 hc7 hc5 hc4 hc3 hc2 hc1
  have hdiff_coeff : (full - drow).1.coeff F.scale.p = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hdiff_mem
  change full.1.coeff F.scale.p = drow.1.coeff F.scale.p
  change full.1.coeff F.scale.p - drow.1.coeff F.scale.p = 0 at hdiff_coeff
  exact sub_eq_zero.mp hdiff_coeff

set_option maxRecDepth 10000 in
/-- Coefficientwise, the terminal Faber invariant is its cleared numerator
times the inverse of the fixed nonzero denominator. -/
theorem faberR5_coeff_eq_fullN5_coeff_div
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 :
      GCD369CubeHahnRegular k) (e : ℚ) :
    (GCD369CubeFaberR5
      (a0 : HahnSeries ℚ k) a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).coeff e =
      (GCD369CubeFaberFullN5
        a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).1.coeff e /
          (13436928 : k) := by
  rw [GCD369CubeFaberR5_eq_fullN5_div, div_eq_mul_inv]
  change
    ((GCD369CubeFaberFullN5
      a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).1 *
        (HahnSeries.C (13436928 : k))⁻¹).coeff e = _
  rw [← map_inv₀]
  change
    ((GCD369CubeFaberFullN5
      a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).1 *
        HahnSeries.single 0 (13436928 : k)⁻¹).coeff e = _
  rw [HahnSeries.coeff_mul_single_zero]
  rw [div_eq_mul_inv]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- In the strict singular window `2 * delta < p < 3 * delta`, the pure
weight-one load is the unique first term of the fifth numerator. -/
theorem fullN5_orderTop_eq_p_of_singular_middle
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale)
    (Kd C7 C5 C4 C3 C2 C1 R1 R2 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (r : k) (hr : r ≠ 0) (hKd : Kd ≠ 0)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (_hmiddle : 2 * T.delta < D.faber.scale.p)
    (hlate : D.faber.scale.p < 3 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.orderTop =
        (↑D.faber.scale.p : WithTop ℚ) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      D.faber.scale.p D.faber.scale.hp.le
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let dload : GCD369CubeHahnRegular k :=
    D.faber.scale.weightedRegular 1 D.faber.d
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 dload
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let Nd : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 dload 0 0 0 0 0 0
  obtain ⟨Rem, hRemCoeff, hrelation⟩ := T.dTerminalRelation
  let Main : GCD369CubeHahnRegular k := dload * Rem
  have hRemCoeff' : GCD369CubeHahnRegular.constantCoeff Rem =
      -554729472 * r ^ 13 := by
    calc
      GCD369CubeHahnRegular.constantCoeff Rem =
          540672 * D.u ^ 5 * D.v - 4055040 * D.u ^ 2 * D.v ^ 3 :=
        hRemCoeff
      _ = -554729472 * r ^ 13 := by
        rw [hu, hv]
        exact GCD369CubeDTerminalResidual_doubleRoot r
  have hload : dload =
      GCD369CubeHahnRegular.monomial
          D.faber.scale.p D.faber.scale.hp.le *
        GCD369CubeHahnRegular.constant Kd := by
    apply Subtype.ext
    dsimp only [dload, GCD369CubeHahnPoleScale.weightedRegular]
    change D.faber.scale.t ^ 1 * D.faber.d.1 =
      HahnSeries.single D.faber.scale.p 1 *
        (GCD369CubeHahnRegular.constant Kd).1
    rw [hd]
    simp [GCD369CubeHahnPoleScale.t]
  have hfactorCoeff :
      GCD369CubeHahnRegular.constantCoeff
          (GCD369CubeHahnRegular.constant Kd * Rem) ≠ 0 := by
    rw [map_mul, GCD369CubeHahnRegular.constantCoeff_constant, hRemCoeff']
    exact mul_ne_zero hKd
      (mul_ne_zero (by norm_num) (pow_ne_zero 13 hr))
  have hMainFactor : Main =
      (GCD369CubeHahnRegular.monomial
          D.faber.scale.p D.faber.scale.hp.le) ^ 1 *
        (GCD369CubeHahnRegular.constant Kd * Rem) := by
    dsimp only [Main]
    rw [hload]
    ring
  have hMainOrder : Main.1.orderTop =
      (↑D.faber.scale.p : WithTop ℚ) := by
    rw [hMainFactor]
    simpa using
      (GCD369CubeHahnRegular.orderTop_monomial_pow_mul_eq_of_constantCoeff_ne
        D.faber.scale.p D.faber.scale.hp 1
        (GCD369CubeHahnRegular.constant Kd * Rem) hfactorCoeff)
  obtain ⟨hN1, hN2⟩ := D.faber.dN12_mem_higherOrderIdeal
    C7 C5 C4 C3 C2 C1 R1 R2
    hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2
  change _ ∈ I at hN1 hN2
  have hterm1 :
      24 * D.cubicU ^ 2 *
        GCD369CubeFaberD1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 dload ∈ I := by
    exact I.mul_mem_left _ hN1
  have hterm2 :
      (-24 * D.cubicV) *
        GCD369CubeFaberD2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 dload ∈ I := by
    exact I.mul_mem_left _ hN2
  have hterm3raw : H ^ 3 *
      (839808 * GCD369CubeNormalRow5Cubic
        T.Xn T.Yn T.Zn D.cubicU) ∈ I := by
    simpa only [H, I] using
      (GCD369CubeHahnRegular.monomial_pow_mul_mem_higherOrderIdeal
        T.delta T.hdelta 3
        (839808 * GCD369CubeNormalRow5Cubic
          T.Xn T.Yn T.Zn D.cubicU)
        D.faber.scale.hp.le hlate)
  have hterm3 : 839808 * H ^ 3 *
      GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU ∈ I := by
    convert hterm3raw using 1 <;> ring
  have hrelation' : Nd =
      24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload -
        24 * D.cubicV *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload +
        839808 * H ^ 3 *
          GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU +
        Main := by
    simpa only [Nd, H, dload, Main] using hrelation
  have hNdMain : Nd - Main ∈ I := by
    have heq : Nd - Main =
        (24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload) +
        ((-24 * D.cubicV) *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload) +
        839808 * H ^ 3 *
          GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU := by
      rw [hrelation']
      ring
    rw [heq]
    exact I.add_mem (I.add_mem hterm1 hterm2) hterm3
  have hNdiff : N - Nd ∈ I := by
    simpa only [N, Nd, dload, I] using
      D.faber.fullN5_sub_dSpecialized_mem_higherOrderIdeal
        C7 C5 C4 C3 C2 C1 hc7 hc5 hc4 hc3 hc2 hc1
  have hNMain : N - Main ∈ I := by
    have heq : N - Main = (N - Nd) + (Nd - Main) := by ring
    rw [heq]
    exact I.add_mem hNdiff hNdMain
  have hsum : N = Main + (N - Main) := by ring
  have hlt : Main.1.orderTop < (N - Main).1.orderTop := by
    rw [hMainOrder]
    exact hNMain
  change N.1.orderTop = (↑D.faber.scale.p : WithTop ℚ)
  rw [hsum]
  change (Main.1 + (N - Main).1).orderTop = _
  rw [HahnSeries.orderTop_add_eq_left hlt, hMainOrder]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- If the weight-one load comes strictly after the cubic transverse term,
the intrinsic singular cubic is the unique first term of the fifth
numerator. -/
theorem fullN5_orderTop_eq_three_delta_of_singular_late
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale)
    (Kd C7 C5 C4 C3 C2 C1 R1 R2 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : D.u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta < D.faber.scale.p) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.orderTop =
        (↑(3 * T.delta) : WithTop ℚ) := by
  have he : 0 ≤ 3 * T.delta :=
    mul_nonneg (by norm_num) T.hdelta.le
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal (3 * T.delta) he
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let dload : GCD369CubeHahnRegular k :=
    D.faber.scale.weightedRegular 1 D.faber.d
  let C : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  let Main : GCD369CubeHahnRegular k := 839808 * H ^ 3 * C
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 dload
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let Nd : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 dload 0 0 0 0 0 0
  obtain ⟨Rem, _hRemCoeff, hrelation⟩ := T.dTerminalRelation
  have hCcoeff : GCD369CubeHahnRegular.constantCoeff C =
      -3 * r ^ 2 * A ^ 3 := by
    dsimp only [C]
    rw [GCD369CubeNormalRow5Cubic_map,
      D.constantCoeff_cubicU, hX, hY, hZ, hu]
    exact GCD369CubeNormalRow5Cubic_doubleRoot r A
  have hfactorCoeff :
      GCD369CubeHahnRegular.constantCoeff (839808 * C) ≠ 0 := by
    rw [map_mul, map_ofNat, hCcoeff]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
        (pow_ne_zero 3 hA))
  have hMainFactor : Main = H ^ 3 * (839808 * C) := by
    dsimp only [Main]
    ring
  have hMainOrder : Main.1.orderTop =
      (↑(3 * T.delta) : WithTop ℚ) := by
    rw [hMainFactor]
    convert
      (GCD369CubeHahnRegular.orderTop_monomial_pow_mul_eq_of_constantCoeff_ne
        T.delta T.hdelta 3 (839808 * C) hfactorCoeff) using 1 <;>
      norm_num [H]
  obtain ⟨hN1p, hN2p⟩ := D.faber.dN12_mem_higherOrderIdeal
    C7 C5 C4 C3 C2 C1 R1 R2
    hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2
  have hN1 :
      GCD369CubeFaberD1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 dload ∈ I := by
    change (↑(3 * T.delta) : WithTop ℚ) < _
    exact (WithTop.coe_lt_coe.mpr hlate).trans hN1p
  have hN2 :
      GCD369CubeFaberD2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 dload ∈ I := by
    change (↑(3 * T.delta) : WithTop ℚ) < _
    exact (WithTop.coe_lt_coe.mpr hlate).trans hN2p
  have hterm1 :
      24 * D.cubicU ^ 2 *
        GCD369CubeFaberD1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 dload ∈ I :=
    I.mul_mem_left _ hN1
  have hterm2 :
      (-24 * D.cubicV) *
        GCD369CubeFaberD2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 dload ∈ I :=
    I.mul_mem_left _ hN2
  have hdload : dload ∈ I := by
    dsimp only [dload, I]
    rw [hd]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      D.faber.scale 1 Kd he (by convert hlate using 1 <;> norm_num)
  have hloadterm : dload * Rem ∈ I := by
    convert I.mul_mem_left Rem hdload using 1 <;> ring
  have hrelation' : Nd =
      24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload -
        24 * D.cubicV *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload +
        Main + dload * Rem := by
    simpa only [Nd, H, dload, C, Main] using hrelation
  have hNdMain : Nd - Main ∈ I := by
    have heq : Nd - Main =
        (24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload) +
        ((-24 * D.cubicV) *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload) +
        dload * Rem := by
      rw [hrelation']
      ring
    rw [heq]
    exact I.add_mem (I.add_mem hterm1 hterm2) hloadterm
  have hNdiffP :=
    D.faber.fullN5_sub_dSpecialized_mem_higherOrderIdeal
      C7 C5 C4 C3 C2 C1 hc7 hc5 hc4 hc3 hc2 hc1
  have hNdiff : N - Nd ∈ I := by
    change (↑(3 * T.delta) : WithTop ℚ) < _
    change (↑D.faber.scale.p : WithTop ℚ) < _ at hNdiffP
    exact (WithTop.coe_lt_coe.mpr hlate).trans (by
      simpa only [N, Nd, dload] using hNdiffP)
  have hNMain : N - Main ∈ I := by
    have heq : N - Main = (N - Nd) + (Nd - Main) := by ring
    rw [heq]
    exact I.add_mem hNdiff hNdMain
  have hsum : N = Main + (N - Main) := by ring
  have hlt : Main.1.orderTop < (N - Main).1.orderTop := by
    rw [hMainOrder]
    exact hNMain
  change N.1.orderTop = (↑(3 * T.delta) : WithTop ℚ)
  rw [hsum]
  change (Main.1 + (N - Main).1).orderTop = _
  rw [HahnSeries.orderTop_add_eq_left hlt, hMainOrder]

set_option maxRecDepth 10000 in
/-- Dividing the cleared fifth numerator by its fixed nonzero scalar does
not change its finite Hahn order. -/
theorem faberR5_order_eq_of_fullN5_orderTop_eq
    {k : Type*} [Field k] [CharZero k]
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 :
      GCD369CubeHahnRegular k) (e : ℚ)
    (hN :
      (GCD369CubeFaberFullN5
        a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).1.orderTop =
          (↑e : WithTop ℚ)) :
    (GCD369CubeFaberR5
      (a0 : HahnSeries ℚ k) a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).order =
        e := by
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1
  let terminal : HahnSeries ℚ k := GCD369CubeFaberR5
    (a0 : HahnSeries ℚ k) a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1
  have hterminal_eq : terminal = N.1 / (13436928 : HahnSeries ℚ k) := by
    dsimp only [terminal, N]
    exact GCD369CubeFaberR5_eq_fullN5_div _ _ _ _ _ _ _ _ _ _ _ _
  have hdenOrder : ((13436928 : HahnSeries ℚ k)⁻¹).orderTop =
      (↑(0 : ℚ) : WithTop ℚ) := by
    change ((HahnSeries.C (13436928 : k))⁻¹).orderTop = _
    rw [← map_inv₀]
    change (HahnSeries.single 0 (13436928 : k)⁻¹).orderTop = _
    rw [HahnSeries.orderTop_single]
    norm_num
  have hterminalOrderTop : terminal.orderTop = (↑e : WithTop ℚ) := by
    rw [hterminal_eq, div_eq_mul_inv, HahnSeries.orderTop_mul]
    change N.1.orderTop + _ = _
    rw [hN, hdenOrder]
    simp
  have hterminal_ne : terminal ≠ 0 := by
    intro hzero
    rw [hzero, HahnSeries.orderTop_zero] at hterminalOrderTop
    exact WithTop.coe_ne_top hterminalOrderTop.symm
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero hterminal_ne,
    hterminalOrderTop]

end GCD369CubeHahnFaberPoleData

namespace GCD369CubePolynomialSource

/-- Source-facing strict weight-one routing at the constant-core infinity
pole. -/
theorem infinity_d_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hbefore :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        2 * T.delta) :
    S.faberConstantParameters.d = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, _hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  apply T.d_eq_zero_before_transverse
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hd
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc7
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc5
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc3
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr4
  · exact hbefore

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A weight-one load cannot tie the first quadratic transverse scale.  The
fifth numerator has a certified nonzero first coefficient, forcing the
impossible constant-pole landing `13 * p = 1`. -/
theorem infinity_d_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (htie :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        2 * T.delta) :
    S.faberConstantParameters.d = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hd
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc7
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc5
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc4
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc3
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc2
  have hc1D : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc1
  have hr1D : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr1
  have hr2D : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr2
  have hr3D : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr3
  have hr4D : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr4
  by_contra hPd
  have hrows := T.dExceptionalRowsAt_at_transverse
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
      hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D htie
  have hterminal := GCD369CubeDExceptionalTerminalAt_nonzero
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn)
    D.u D.v P.d hPd hrows
  have hu := GCD369CubeDExceptionalRowsAt_u_ne_zero
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn)
    D.u D.v P.d hPd hrows
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let Nd : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d) 0 0 0 0 0 0
  have hNdcoeff : Nd.1.coeff D.faber.scale.p =
      768 * GCD369CubeDExceptionalTerminalAt
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn)
        D.u D.v P.d := by
    simpa only [Nd] using T.dTerminalCoeff_at_transverse P.d hdD htie
  have hNdcoeff_ne : Nd.1.coeff D.faber.scale.p ≠ 0 := by
    rw [hNdcoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hNcoeff : N.1.coeff D.faber.scale.p =
      Nd.1.coeff D.faber.scale.p := by
    simpa only [N, Nd] using D.faber.fullN5Coeff_eq_dSpecialized
      P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      hc7D hc5D hc4D hc3D hc2D hc1D
  have hNcoeff_ne : N.1.coeff D.faber.scale.p ≠ 0 := by
    rw [hNcoeff]
    exact hNdcoeff_ne
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5 T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      245760 * D.cubicU ^ 2 * D.cubicV *
        (D.cubicU ^ 3 - 9 * D.cubicV ^ 2) *
          GCD369CubeHahnRegular.constant P.d
  obtain ⟨E, hfactor⟩ := T.dTerminalFactor_at_transverse P.d hdD htie
  change Nd = H ^ 2 * K + H ^ 3 * E at hfactor
  have hNdfactor : Nd = H ^ 2 * (K + H * E) := by
    rw [hfactor]
    ring
  have hNdLower : (↑D.faber.scale.p : WithTop ℚ) ≤ Nd.1.orderTop := by
    rw [hNdfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_sq_mul_lower
      T.delta T.hdelta (K + H * E)
  have hdiff_mem : N - Nd ∈
      GCD369CubeHahnRegular.higherOrderIdeal
        D.faber.scale.p D.faber.scale.hp.le := by
    simpa only [N, Nd] using
      D.faber.fullN5_sub_dSpecialized_mem_higherOrderIdeal
        P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
        hc7D hc5D hc4D hc3D hc2D hc1D
  have hdiffLower : (↑D.faber.scale.p : WithTop ℚ) ≤
      (N - Nd).1.orderTop := hdiff_mem.le
  have hNsum : N = Nd + (N - Nd) := by ring
  have hNLower : (↑D.faber.scale.p : WithTop ℚ) ≤ N.1.orderTop := by
    rw [hNsum]
    exact (le_min hNdLower hdiffLower).trans
      HahnSeries.min_orderTop_le_orderTop_add
  have hNorderTop : N.1.orderTop =
      (↑D.faber.scale.p : WithTop ℚ) :=
    le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero hNcoeff_ne) hNLower
  let terminal : HahnSeries ℚ k := GCD369CubeFaberR5
    (D.faber.scale.regular0 : HahnSeries ℚ k)
    D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  have hterminal_eq : terminal =
      N.1 / (13436928 : HahnSeries ℚ k) := by
    dsimp only [terminal, N]
    exact GCD369CubeFaberR5_eq_fullN5_div _ _ _ _ _ _ _ _ _ _ _ _
  have hdenOrder : ((13436928 : HahnSeries ℚ k)⁻¹).orderTop =
      (↑(0 : ℚ) : WithTop ℚ) := by
    change ((HahnSeries.C (13436928 : k))⁻¹).orderTop = _
    rw [← map_inv₀]
    change (HahnSeries.single 0 (13436928 : k)⁻¹).orderTop = _
    rw [HahnSeries.orderTop_single]
    norm_num
  have hterminalOrderTop : terminal.orderTop =
      (↑D.faber.scale.p : WithTop ℚ) := by
    rw [hterminal_eq, div_eq_mul_inv, HahnSeries.orderTop_mul,
      hNorderTop, hdenOrder]
    norm_num
  have hterminal_ne : terminal ≠ 0 := by
    intro hzero
    rw [hzero, HahnSeries.orderTop_zero] at hterminalOrderTop
    exact WithTop.coe_ne_top hterminalOrderTop.symm
  have hterminalOrder : terminal.order = D.faber.scale.p := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hterminal_ne,
      hterminalOrderTop]
  have hscaled : terminal =
      D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  have hfirst :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity
          S.terminalFaberInvariant).order =
        1 * D.faber.scale.p := by
    rw [← hscaled]
    simpa using hterminalOrder
  have hscale : 13 *
      (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [Nat.cast_one, sub_self, one_mul, show (14 : ℚ) - 1 = 13 by norm_num,
      D, S.infinityCommonCoefficientData_faber hsdegree] using
        S.infinity_terminal_scale_eq_of_order_eq_weight
          hsdegree hpole 1 hfirst
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu
  have h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h4D
  have hlanding : GCD369CubeConstantPoleDegreeLanding :=
    S.infinityConstantPoleDegreeLanding_of_d_scale
      hsdegree hpole hscale h4
  exact GCD369CubeConstantPoleDegreeLandingEmpty hlanding

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero weight-one load is impossible in the strict singular window
between the quadratic and cubic transverse exponents. -/
theorem infinity_d_eq_zero_singular_middle
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hmiddle : 2 * T.delta <
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p)
    (hlate : (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
      3 * T.delta) :
    S.faberConstantParameters.d = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hd
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc7
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc5
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc4
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc3
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc2
  have hc1D : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc1
  have hr1D : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr1
  have hr2D : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr2
  have hr3D : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr3
  have hr4D : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr4
  by_contra hPd
  have hrows := T.zeroLoadLeadingRows_before_d
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D hmiddle
  obtain ⟨r, hA, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading hrows.1 hrows.2.1 hrows.2.2.1 hrows.2.2.2
  have hr : r ≠ 0 := by
    intro hzero
    have hu0 : D.u = 0 := by rw [hu, hzero]; norm_num
    have hv0 : D.v = 0 := by rw [hv, hzero]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hNorder :=
    GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_p_of_singular_middle
      D T P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2
      hdD hc7D hc5D hc4D hc3D hc2D hc1D hr1D hr2D
      r hr hPd hu hv hmiddle hlate
  have hterminalOrder :
      (GCD369CubeFaberR5
        (D.faber.scale.regular0 : HahnSeries ℚ k)
        D.faber.scale.regular1 D.faber.scale.regular2
        D.faber.scale.regular3 D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1)).order =
          D.faber.scale.p :=
    GCD369CubeHahnFaberPoleData.faberR5_order_eq_of_fullN5_orderTop_eq
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)
      D.faber.scale.p hNorder
  have hscaled :
      GCD369CubeFaberR5
        (D.faber.scale.regular0 : HahnSeries ℚ k)
        D.faber.scale.regular1 D.faber.scale.regular2
        D.faber.scale.regular3 D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1) =
      D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change _ = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  have hfirst :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          1 * D.faber.scale.p := by
    rw [← hscaled]
    simpa using hterminalOrder
  have hscale : 13 *
      (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [Nat.cast_one, sub_self, one_mul,
      show (14 : ℚ) - 1 = 13 by norm_num,
      D, S.infinityCommonCoefficientData_faber hsdegree] using
        S.infinity_terminal_scale_eq_of_order_eq_weight
          hsdegree hpole 1 hfirst
  have hu_ne : D.u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu_ne
  have h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h4D
  have hlanding : GCD369CubeConstantPoleDegreeLanding :=
    S.infinityConstantPoleDegreeLanding_of_d_scale
      hsdegree hpole hscale h4
  exact GCD369CubeConstantPoleDegreeLandingEmpty hlanding

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A weight-one load is also impossible strictly after the cubic
transverse exponent: the terminal order and the integral fourth-coefficient
degree give incompatible bounds for the pole scale. -/
theorem infinity_d_eq_zero_singular_late
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hmiddle : 2 * T.delta <
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p)
    (hlate : 3 * T.delta <
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    S.faberConstantParameters.d = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hd
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc7
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc5
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc4
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc3
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc2
  have hc1D : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc1
  have hr1D : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr1
  have hr2D : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr2
  have hr3D : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr3
  have hr4D : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr4
  by_contra _hPd
  have hrows := T.zeroLoadLeadingRows_before_d
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D hmiddle
  obtain ⟨r, hA, hu, _hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading hrows.1 hrows.2.1 hrows.2.2.1 hrows.2.2.2
  have hr : r ≠ 0 := by
    intro hzero
    have hu0 : D.u = 0 := by rw [hu, hzero]; norm_num
    have hv0 : D.v = 0 := by rw [_hv, hzero]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hNorder :=
    GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_late
      D T P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2
      hdD hc7D hc5D hc4D hc3D hc2D hc1D hr1D hr2D
      r (GCD369CubeHahnRegular.constantCoeff T.Xn) hr hA
      hu rfl hY hZ hlate
  have hterminalOrder :
      (GCD369CubeFaberR5
        (D.faber.scale.regular0 : HahnSeries ℚ k)
        D.faber.scale.regular1 D.faber.scale.regular2
        D.faber.scale.regular3 D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1)).order =
          3 * T.delta :=
    GCD369CubeHahnFaberPoleData.faberR5_order_eq_of_fullN5_orderTop_eq
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)
      (3 * T.delta) hNorder
  have hscaled :
      GCD369CubeFaberR5
        (D.faber.scale.regular0 : HahnSeries ℚ k)
        D.faber.scale.regular1 D.faber.scale.regular2
        D.faber.scale.regular3 D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1) =
      D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change _ = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  have hscaledOrder :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          3 * T.delta := by
    rw [← hscaled]
    exact hterminalOrder
  have hglobal :=
    S.infinityFaberPoleData_scaled_terminal_order hsdegree hpole
  change
    (D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
        14 * D.faber.scale.p - 1 at hglobal
  have hscaleEq : 14 * D.faber.scale.p - 1 = 3 * T.delta := by
    calc
      14 * D.faber.scale.p - 1 =
          (D.faber.scale.t ^ 14 *
            GCD369CubeRatFuncHahnAtInfinity
              S.terminalFaberInvariant).order := hglobal.symm
      _ = 3 * T.delta := hscaledOrder
  have hu_ne : D.u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu_ne
  have h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h4D
  let n : ℕ := (S.constantCoreNormalizedPPolynomial.coeff 4).natDegree
  have hn : (n : ℚ) = 2 * D.faber.scale.p := by
    simpa only [n, D, S.infinityCommonCoefficientData_faber hsdegree] using
      S.infinityLeading4_natDegree hsdegree hpole h4
  have hn0 : n ≠ 0 := by
    intro hzero
    have hpzero : D.faber.scale.p = 0 := by
      have := hn
      rw [hzero] at this
      norm_num at this
      linarith
    exact ne_of_gt D.faber.scale.hp hpzero
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
  have hpHalf : (1 : ℚ) / 2 ≤ D.faber.scale.p := by
    rw [hn] at hn1
    linarith
  linarith

end GCD369CubePolynomialSource
