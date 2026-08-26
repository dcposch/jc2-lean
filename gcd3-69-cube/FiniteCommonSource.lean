import FiniteBoundarySource

noncomputable section
open Polynomial

/-! # Common-cubic finite-pole jets

The original boundary values force every finite leading pole onto the
common-cubic component.  This file begins the next, genuinely infinitesimal,
step.  It records the limiting cubic root and proves that every nonzero
zero-load normal satisfying the four Faber quadrics shares a root with that
cubic.  Thus such a normal is not an early obstruction; it is precisely the
root-following branch that must be lifted until the first nonzero target
load.
-/

/-- A nonzero common-normal vector satisfying the four zero-load Faber rows
lies on the unique singular-cubic tangent branch. -/
theorem GCD369CubeZeroLoadNormal_parametrization
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (hnonzero : Xn ≠ 0 ∨ Yn ≠ 0 ∨ Zn ≠ 0)
    (h1 : GCD369CubeNormalRow1 Xn Yn Zn u = 0)
    (h2 : GCD369CubeNormalRow2 Xn Yn Zn u v = 0)
    (h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0)
    (_h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0) :
    ∃ r : K,
      Xn ≠ 0 ∧ u = -3 * r ^ 2 ∧ v = 2 * r ^ 3 ∧
      Yn = r * Xn ∧ Zn = -2 * r ^ 2 * Xn := by
  have he1 : u * Xn ^ 2 - 2 * Xn * Zn - Yn ^ 2 = 0 := by
    dsimp [GCD369CubeNormalRow1] at h1
    linear_combination (1 / 729) * h1
  have he2 : v * Xn ^ 2 + 2 * u * Xn * Yn - 2 * Yn * Zn = 0 := by
    dsimp [GCD369CubeNormalRow2] at h2
    linear_combination (-1 / 2187) * h2
  have he3 : Zn ^ 2 - 2 * v * Xn * Yn = 0 := by
    dsimp [GCD369CubeNormalRow3] at h3
    linear_combination (1 / 3) * h3 - (2 * u / 3) * he1
  have hX : Xn ≠ 0 := by
    intro hX
    have hY : Yn = 0 := by
      rw [hX] at he1
      norm_num at he1
      exact he1
    have hZ : Zn = 0 := by
      rw [hX, hY] at he3
      norm_num at he3
      exact he3
    exact hnonzero.elim (fun h => h hX)
      (fun h => h.elim (fun h => h hY) (fun h => h hZ))
  have hsquare : (Xn * Zn + 2 * Yn ^ 2) ^ 2 = 0 := by
    linear_combination Xn ^ 2 * he3 + 2 * Xn * Yn * he2 -
      4 * Yn ^ 2 * he1
  have hnormal : Xn * Zn + 2 * Yn ^ 2 = 0 :=
    (sq_eq_zero_iff).mp hsquare
  let r := Yn / Xn
  have hu : u = -3 * r ^ 2 := by
    dsimp only [r]
    field_simp [hX]
    linear_combination he1 + 2 * hnormal
  have hZ : Zn = -2 * r ^ 2 * Xn := by
    dsimp only [r]
    field_simp [hX]
    linear_combination hnormal
  have hv : v = 2 * r ^ 3 := by
    dsimp only [r] at hu hZ ⊢
    field_simp [hX] at hu hZ ⊢
    linear_combination Xn * he2 - 2 * Yn * hu + 2 * Yn * hZ
  refine ⟨r, hX, hu, hv, ?_, hZ⟩
  · dsimp only [r]
    field_simp [hX]

/-- In particular, the zero-load normal quadratic and the limiting cubic
share their distinguished singular root. -/
theorem GCD369CubeZeroLoadNormal_commonRoot
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (hnonzero : Xn ≠ 0 ∨ Yn ≠ 0 ∨ Zn ≠ 0)
    (h1 : GCD369CubeNormalRow1 Xn Yn Zn u = 0)
    (h2 : GCD369CubeNormalRow2 Xn Yn Zn u v = 0)
    (h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0)
    (h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0) :
    ∃ r : K,
      r ^ 3 + u * r + v = 0 ∧
      Xn * r ^ 2 + Yn * r + Zn = 0 := by
  obtain ⟨r, _hX, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      Xn Yn Zn u v hnonzero h1 h2 h3 h4
  refine ⟨r, ?_, ?_⟩
  · rw [hu, hv]
    ring
  · rw [hY, hZ]
    ring

/-- The singular cubic and its zero-load normal quadratic have the exact
factorizations exposed by the parametrization. -/
theorem GCD369CubeZeroLoadNormal_factorization
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v x : K)
    (hnonzero : Xn ≠ 0 ∨ Yn ≠ 0 ∨ Zn ≠ 0)
    (h1 : GCD369CubeNormalRow1 Xn Yn Zn u = 0)
    (h2 : GCD369CubeNormalRow2 Xn Yn Zn u v = 0)
    (h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0)
    (h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0) :
    ∃ r : K, Xn ≠ 0 ∧
      x ^ 3 + u * x + v = (x - r) ^ 2 * (x + 2 * r) ∧
      Xn * x ^ 2 + Yn * x + Zn = Xn * (x - r) * (x + 2 * r) := by
  obtain ⟨r, hX, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      Xn Yn Zn u v hnonzero h1 h2 h3 h4
  refine ⟨r, hX, ?_, ?_⟩
  · rw [hu, hv]
    ring
  · rw [hY, hZ]
    ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The ninth Faber value along an arbitrary common-normal arc agrees to
first order with `K^3 + (3/2) H K Φ`; the remaining polynomial is divisible
by `H^2`.  The statement works over any commutative ring carrying explicit
rational constants, so it can later be instantiated in the regular Hahn
local ring. -/
theorem GCD369CubeFaberNineCommonNormalExpansionQ
    {R : Type*} [CommRing R] (q : ℚ →+* R)
    (Xn Yn Zn u v x : R) :
    let H : R[X] := X
    let A0 : R[X] := C (v ^ 2) + C Zn * H
    let A1 : R[X] := C (2 * u * v) + C Yn * H
    let A2 : R[X] := C (u ^ 2) + C Xn * H
    let A3 : R[X] := C (2 * v)
    let A4 : R[X] := C (2 * u)
    let Kval := x ^ 3 + u * x + v
    let phival := Xn * x ^ 2 + Yn * x + Zn
    ∃ E : R[X],
      GCD369CubeFaberNineValueQ
          ((Polynomial.C : R →+* R[X]).comp q)
          A0 A1 A2 A3 A4 (C x) =
        C (Kval ^ 3) + C (q (3 / 2) * Kval * phival) * H + H ^ 2 * E := by
  dsimp only
  have qscale (r : ℚ) : q r = q (128 * r) * q (1 / 128) := by
    rw [← q.map_mul]
    congr 1
    ring
  have hunit : (128 : R) * q (1 / 128) = 1 := by
    rw [show (128 : R) = q 128 by exact (map_ofNat q 128).symm,
      ← q.map_mul]
    norm_num
  let P : R[X] :=
    GCD369CubeFaberNineValueQ
        ((Polynomial.C : R →+* R[X]).comp q)
        (C (v ^ 2) + C Zn * X)
        (C (2 * u * v) + C Yn * X)
        (C (u ^ 2) + C Xn * X) (C (2 * v)) (C (2 * u)) (C x) -
      (C ((x ^ 3 + u * x + v) ^ 3) +
        C (q (3 / 2) * (x ^ 3 + u * x + v) *
          (Xn * x ^ 2 + Yn * x + Zn)) * X)
  have h0 : P.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [P, GCD369CubeFaberNineValueQ, RingHom.comp_apply,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
      mul_zero, add_zero]
    rw [qscale (3 / 4), qscale (3 / 16), qscale (3 / 8),
      qscale (3 / 128), qscale (3 / 2), qscale (1 / 16),
      qscale (3 / 32)]
    norm_num
    rw [map_ofNat q 96, map_ofNat q 24, map_ofNat q 48,
      map_ofNat q 3, map_ofNat q 192, map_ofNat q 8, map_ofNat q 12]
    ring_nf
    linear_combination
      (3 * x * u * v ^ 2 + 3 * x ^ 2 * u ^ 2 * v + x ^ 3 * u ^ 3 +
        3 * x ^ 3 * v ^ 2 + 6 * x ^ 4 * u * v + 3 * x ^ 5 * u ^ 2 +
        3 * x ^ 6 * v + 3 * x ^ 7 * u + v ^ 3) * hunit
  have h1 : P.coeff 1 = 0 := by
    calc
      P.coeff 1 = P.derivative.eval 0 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        norm_num [Polynomial.coeff_derivative]
      _ = 0 := by
        simp only [P, GCD369CubeFaberNineValueQ, RingHom.comp_apply,
          Polynomial.derivative_sub, Polynomial.derivative_add,
          Polynomial.derivative_mul, Polynomial.derivative_pow,
          Polynomial.derivative_C, Polynomial.derivative_X,
          Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_zero, zero_mul, mul_zero, zero_add, add_zero,
          mul_one]
        rw [qscale (3 / 2), qscale (3 / 8), qscale (3 / 16),
          qscale (3 / 4)]
        norm_num
        rw [map_ofNat q 192, map_ofNat q 48, map_ofNat q 24,
          map_ofNat q 96]
        ring_nf
  have hdiv : (X : R[X]) ^ 2 ∣ P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> assumption
  obtain ⟨E, hE⟩ := hdiv
  refine ⟨E, ?_⟩
  dsimp only [P] at hE
  linear_combination hE

/-- The four zero-high common-normal numerator expansions require only a
commutative ring.  This version can therefore be instantiated directly in
the regular Hahn local ring, retaining certified regular cubic errors. -/
theorem GCD369CubeFaberCommonNormalNumeratorsCommRing
    {R : Type*} [CommRing R] (Xn Yn Zn u v : R) :
    let H : R[X] := X
    let A0 : R[X] := C (v ^ 2) + C Zn * H
    let A1 : R[X] := C (2 * u * v) + C Yn * H
    let A2 : R[X] := C (u ^ 2) + C Xn * H
    let A3 : R[X] := C (2 * v)
    let A4 : R[X] := C (2 * u)
    729 * GCD369CubeFaberN1 A0 A1 A2 A3 A4 =
        C (-32 * GCD369CubeNormalRow1 Xn Yn Zn u) * H ^ 2 ∧
    2187 * GCD369CubeFaberN2 A0 A1 A2 A3 A4 =
        C (32 * GCD369CubeNormalRow2 Xn Yn Zn u v) * H ^ 2 ∧
    GCD369CubeFaberN3 A0 A1 A2 A3 A4 =
        C (128 * GCD369CubeNormalRow3 Xn Yn Zn u v) * H ^ 2 -
          C (64 * Xn ^ 3) * H ^ 3 ∧
    6561 * GCD369CubeFaberN4 A0 A1 A2 A3 A4 =
        C (32 * GCD369CubeNormalRow4 Xn Yn Zn u v) * H ^ 2 -
          C (314928 * Yn * Xn ^ 2) * H ^ 3 := by
  dsimp only
  constructor
  · simp only [GCD369CubeFaberN1, GCD369CubeNormalRow1]
    simp only [C_mul, C_pow, C_neg, C_sub, C_ofNat]
    ring
  constructor
  · simp only [GCD369CubeFaberN2, GCD369CubeNormalRow2]
    simp only [C_add, C_mul, C_pow, C_neg, C_sub, C_ofNat]
    ring
  constructor
  · simp only [GCD369CubeFaberN3, GCD369CubeNormalRow3]
    simp only [C_add, C_mul, C_pow, C_sub, C_ofNat]
    ring
  · simp only [GCD369CubeFaberN4, GCD369CubeNormalRow4]
    simp only [C_add, C_mul, C_pow, C_sub, C_ofNat]
    ring

/-- The fourth primitive numerator commutes with arbitrary commutative-ring
homomorphisms. -/
theorem GCD369CubeFaberN4_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 : R) :
    f (GCD369CubeFaberN4 a0 a1 a2 a3 a4) =
      GCD369CubeFaberN4 (f a0) (f a1) (f a2) (f a3) (f a4) := by
  simp only [GCD369CubeFaberN4, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat]

namespace GCD369CubeHahnRegular

/-- The explicit rational constants in the regular local ring satisfy the
expected inverse relation for two. -/
theorem two_mul_ratCast_half
    {k : Type*} [Field k] [CharZero k] :
    (2 : GCD369CubeHahnRegular k) *
      GCD369CubeHahnRegular.ratCast (1 / 2) = 1 := by
  have htwo : (2 : GCD369CubeHahnRegular k) =
      GCD369CubeHahnRegular.constant (2 : k) := by
    apply Subtype.ext
    exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 2).symm
  have hrat : GCD369CubeHahnRegular.ratCast (1 / 2) =
      GCD369CubeHahnRegular.constant (1 / 2 : k) := by
    change GCD369CubeHahnRegular.constant (algebraMap ℚ k (1 / 2)) =
      GCD369CubeHahnRegular.constant (1 / 2 : k)
    congr 1
    norm_num
  calc
    _ = GCD369CubeHahnRegular.constant (2 : k) *
        GCD369CubeHahnRegular.constant (1 / 2 : k) := by rw [htwo, hrat]
    _ = GCD369CubeHahnRegular.constant ((2 : k) * (1 / 2 : k)) :=
      ((GCD369CubeHahnRegular.constant (k := k)).map_mul _ _).symm
    _ = 1 := by norm_num

/-- A regular Hahn series with zero residue has strictly positive extended
order (with the zero series represented by `\top`). -/
theorem orderTop_pos_of_constantCoeff_zero
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (hx : GCD369CubeHahnRegular.constantCoeff x = 0) :
    (↑(0 : ℚ) : WithTop ℚ) < x.1.orderTop := by
  apply lt_of_le_of_ne x.2
  exact (HahnSeries.orderTop_ne_of_coeff_eq_zero hx).symm

/-- A nonnegative Hahn monomial, packaged in the regular local ring. -/
def monomial {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 ≤ delta) :
    GCD369CubeHahnRegular k :=
  ⟨HahnSeries.single delta 1, by
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single delta (1 : k)).orderTop
    rw [HahnSeries.orderTop_single one_ne_zero]
    exact_mod_cast hdelta⟩

/-- Divide a regular series by a Hahn monomial whose exponent does not
exceed its order.  The quotient stays in the regular local ring. -/
def shift {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ)
    (hdelta : (↑delta : WithTop ℚ) ≤ x.1.orderTop) :
    GCD369CubeHahnRegular k :=
  ⟨HahnSeries.single (-delta) 1 * x.1, by
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      (HahnSeries.single (-delta) (1 : k) * x.1).orderTop
    rw [HahnSeries.orderTop_mul,
      HahnSeries.orderTop_single one_ne_zero]
    have h := add_le_add_left hdelta (↑(-delta) : WithTop ℚ)
    simpa [add_comm] using h⟩

/-- Shifting and then restoring the selected monomial recovers the original
regular series exactly. -/
theorem monomial_mul_shift
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ) (hdelta0 : 0 ≤ delta)
    (hdelta : (↑delta : WithTop ℚ) ≤ x.1.orderTop) :
    monomial delta hdelta0 * shift x delta hdelta = x := by
  apply Subtype.ext
  change HahnSeries.single delta 1 *
      (HahnSeries.single (-delta) 1 * x.1) = x.1
  rw [← mul_assoc, HahnSeries.single_mul_single]
  simp

/-- The residue after shifting by `delta` is the original coefficient at
that exponent. -/
theorem constantCoeff_shift
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ)
    (hdelta : (↑delta : WithTop ℚ) ≤ x.1.orderTop) :
    GCD369CubeHahnRegular.constantCoeff (shift x delta hdelta) =
      x.1.coeff delta := by
  change (HahnSeries.single (-delta) 1 * x.1).coeff 0 = x.1.coeff delta
  rw [HahnSeries.coeff_single_mul]
  simp

/-- Shifting by the exact finite order exposes a nonzero residue. -/
theorem constantCoeff_shift_ne_zero
    {k : Type*} [Field k]
    (x : GCD369CubeHahnRegular k) (delta : ℚ)
    (horder : x.1.orderTop = (↑delta : WithTop ℚ)) :
    GCD369CubeHahnRegular.constantCoeff
        (shift x delta horder.symm.le) ≠ 0 := by
  rw [constantCoeff_shift]
  exact HahnSeries.coeff_orderTop_ne horder

/-- Regular Hahn series have no coefficients at negative exponents. -/
theorem coeff_eq_zero_of_neg
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    {e : ℚ} (he : e < 0) : x.1.coeff e = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  exact (WithTop.coe_lt_coe.mpr he).trans_le x.2

/-- At the exact exponent of a positive monomial power, multiplication by a
regular series exposes that series' residue. -/
theorem coeff_monomial_pow_mul_at
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta) (n : ℕ)
    (x : GCD369CubeHahnRegular k) :
    ((monomial delta hdelta.le) ^ n * x).1.coeff ((n : ℚ) * delta) =
      GCD369CubeHahnRegular.constantCoeff x := by
  change ((HahnSeries.single delta (1 : k)) ^ n * x.1).coeff
      ((n : ℚ) * delta) = x.1.coeff 0
  rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
  simp [nsmul_eq_mul]

/-- A higher positive monomial power contributes nothing at the exponent of
a lower power when its remaining factor is regular. -/
theorem coeff_monomial_pow_mul_of_lt
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta)
    (m n : ℕ) (hmn : m < n) (x : GCD369CubeHahnRegular k) :
    ((monomial delta hdelta.le) ^ n * x).1.coeff ((m : ℚ) * delta) = 0 := by
  change ((HahnSeries.single delta (1 : k)) ^ n * x.1).coeff
      ((m : ℚ) * delta) = 0
  rw [HahnSeries.single_pow, HahnSeries.coeff_single_mul]
  simp only [one_pow, one_mul]
  apply coeff_eq_zero_of_neg x
  rw [nsmul_eq_mul]
  have hcast : (m : ℚ) < n := by exact_mod_cast hmn
  nlinarith

end GCD369CubeHahnRegular

/-- A scaled original-value packet together with its certified nonzero
common-cubic leading component. -/
structure GCD369CubeHahnCommonValueData
    (k : Type*) [Field k] [CharZero k] where
  normal : GCD369CubeHahnNormalValueData k
  u : k
  v : k
  hprojective : u ≠ 0 ∨ v ≠ 0
  ha4 : normal.sextic.scale.leading4 = 2 * u
  ha3 : normal.sextic.scale.leading3 = 2 * v
  ha2 : normal.sextic.scale.leading2 = u ^ 2
  ha1 : normal.sextic.scale.leading1 = 2 * u * v
  ha0 : normal.sextic.scale.leading0 = v ^ 2

namespace GCD369CubeHahnCommonValueData

/-- The moving cubic coefficients read directly from the scaled sextic. -/
def cubicU {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.ratCast (1 / 2) * S.normal.sextic.scale.regular4

def cubicV {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  GCD369CubeHahnRegular.ratCast (1 / 2) * S.normal.sextic.scale.regular3

/-- Exact normal coordinates transverse to the moving common-cubic square. -/
def normal2 {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.scale.regular2 - S.cubicU ^ 2

def normal1 {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.scale.regular1 - 2 * S.cubicU * S.cubicV

def normal0 {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.scale.regular0 - S.cubicV ^ 2

/-- The top two scaled sextic coefficients are exactly twice the moving
cubic coefficients. -/
theorem regular4_eq_two_cubicU
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    S.normal.sextic.scale.regular4 = 2 * S.cubicU := by
  dsimp only [cubicU]
  linear_combination
    -S.normal.sextic.scale.regular4 *
      (GCD369CubeHahnRegular.two_mul_ratCast_half (k := k))

theorem regular3_eq_two_cubicV
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    S.normal.sextic.scale.regular3 = 2 * S.cubicV := by
  dsimp only [cubicV]
  linear_combination
    -S.normal.sextic.scale.regular3 *
      (GCD369CubeHahnRegular.two_mul_ratCast_half (k := k))

/-- A first nonzero transverse common-cubic jet, normalized by its exact
positive Hahn order.  At least one of the three normalized coefficients has
nonzero residue. -/
structure TransverseScale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) where
  delta : ℚ
  hdelta : 0 < delta
  Xn : GCD369CubeHahnRegular k
  Yn : GCD369CubeHahnRegular k
  Zn : GCD369CubeHahnRegular k
  hnormal2 : S.normal2 =
    GCD369CubeHahnRegular.monomial delta hdelta.le * Xn
  hnormal1 : S.normal1 =
    GCD369CubeHahnRegular.monomial delta hdelta.le * Yn
  hnormal0 : S.normal0 =
    GCD369CubeHahnRegular.monomial delta hdelta.le * Zn
  hleading :
    GCD369CubeHahnRegular.constantCoeff Xn ≠ 0 ∨
    GCD369CubeHahnRegular.constantCoeff Yn ≠ 0 ∨
    GCD369CubeHahnRegular.constantCoeff Zn ≠ 0

/-- Reconstruct the lower three scaled sextic coefficients from a normalized
transverse jet. -/
theorem TransverseScale.regular2_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    S.normal.sextic.scale.regular2 = S.cubicU ^ 2 + T.Xn *
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le := by
  have hn := T.hnormal2
  dsimp only [normal2] at hn
  linear_combination hn

theorem TransverseScale.regular1_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    S.normal.sextic.scale.regular1 = 2 * S.cubicU * S.cubicV + T.Yn *
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le := by
  have hn := T.hnormal1
  dsimp only [normal1] at hn
  linear_combination hn

theorem TransverseScale.regular0_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    S.normal.sextic.scale.regular0 = S.cubicV ^ 2 + T.Zn *
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le := by
  have hn := T.hnormal0
  dsimp only [normal0] at hn
  linear_combination hn

/-- The moving cubic and its transverse quadratic evaluated at the recovered
scaled source coordinate. -/
def cubicValue {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal.sextic.regularX ^ 3 +
    S.cubicU * S.normal.sextic.regularX + S.cubicV

def transverseValue {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) : GCD369CubeHahnRegular k :=
  S.normal2 * S.normal.sextic.regularX ^ 2 +
    S.normal1 * S.normal.sextic.regularX + S.normal0

/-- The three exact transverse normal coordinates all have zero residue. -/
theorem normal_constantCoeff_zero
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    GCD369CubeHahnRegular.constantCoeff S.normal2 = 0 ∧
    GCD369CubeHahnRegular.constantCoeff S.normal1 = 0 ∧
    GCD369CubeHahnRegular.constantCoeff S.normal0 = 0 := by
  have hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = S.u := by
    simp only [cubicU, map_mul,
      GCD369CubeHahnRegular.constantCoeff_ratCast]
    change algebraMap ℚ k (1 / 2) * S.normal.sextic.scale.leading4 = S.u
    rw [S.ha4]
    norm_num
    ring
  have hv : GCD369CubeHahnRegular.constantCoeff S.cubicV = S.v := by
    simp only [cubicV, map_mul,
      GCD369CubeHahnRegular.constantCoeff_ratCast]
    change algebraMap ℚ k (1 / 2) * S.normal.sextic.scale.leading3 = S.v
    rw [S.ha3]
    norm_num
    ring
  constructor
  · simp only [normal2, map_sub, map_pow, hu]
    change S.normal.sextic.scale.leading2 - S.u ^ 2 = 0
    rw [S.ha2, sub_self]
  constructor
  · simp only [normal1, map_sub, map_mul, map_ofNat, hu, hv]
    change S.normal.sextic.scale.leading1 - 2 * S.u * S.v = 0
    rw [S.ha1, sub_self]
  · simp only [normal0, map_sub, map_pow, hv]
    change S.normal.sextic.scale.leading0 - S.v ^ 2 = 0
    rw [S.ha0, sub_self]

/-- If the exact sextic is not already a moving cubic square, its three
transverse coordinates have a canonical first positive order and normalized
leading jet. -/
noncomputable def transverseScale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k)
    (hnonzero : S.normal2 ≠ 0 ∨ S.normal1 ≠ 0 ∨ S.normal0 ≠ 0) :
    S.TransverseScale := by
  let o2 : WithTop ℚ := S.normal2.1.orderTop
  let o1 : WithTop ℚ := S.normal1.1.orderTop
  let o0 : WithTop ℚ := S.normal0.1.orderTop
  let D : WithTop ℚ := min (min o2 o1) o0
  have hD2 : D ≤ o2 := by
    dsimp only [D]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hD1 : D ≤ o1 := by
    dsimp only [D]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hD0 : D ≤ o0 := by
    dsimp only [D]
    exact min_le_right _ _
  have hDne : D ≠ ⊤ := by
    intro hDtop
    rcases hnonzero with h2 | h1 | h0
    · have h2' : S.normal2.1 ≠ 0 := by
        intro hz
        apply h2
        exact Subtype.ext hz
      have ho2 : o2 = ⊤ := top_unique (hDtop ▸ hD2)
      exact (HahnSeries.orderTop_ne_top.mpr h2') ho2
    · have h1' : S.normal1.1 ≠ 0 := by
        intro hz
        apply h1
        exact Subtype.ext hz
      have ho1 : o1 = ⊤ := top_unique (hDtop ▸ hD1)
      exact (HahnSeries.orderTop_ne_top.mpr h1') ho1
    · have h0' : S.normal0.1 ≠ 0 := by
        intro hz
        apply h0
        exact Subtype.ext hz
      have ho0 : o0 = ⊤ := top_unique (hDtop ▸ hD0)
      exact (HahnSeries.orderTop_ne_top.mpr h0') ho0
  let delta : ℚ := D.untop hDne
  have hdelta_coe : (↑delta : WithTop ℚ) = D := by
    exact WithTop.coe_untop D hDne
  obtain ⟨hz2, hz1, hz0⟩ := S.normal_constantCoeff_zero
  have hp2 : (↑(0 : ℚ) : WithTop ℚ) < o2 :=
    GCD369CubeHahnRegular.orderTop_pos_of_constantCoeff_zero S.normal2 hz2
  have hp1 : (↑(0 : ℚ) : WithTop ℚ) < o1 :=
    GCD369CubeHahnRegular.orderTop_pos_of_constantCoeff_zero S.normal1 hz1
  have hp0 : (↑(0 : ℚ) : WithTop ℚ) < o0 :=
    GCD369CubeHahnRegular.orderTop_pos_of_constantCoeff_zero S.normal0 hz0
  have hDpos : (↑(0 : ℚ) : WithTop ℚ) < D := by
    dsimp only [D]
    exact lt_min (lt_min hp2 hp1) hp0
  have hdelta_top : (↑(0 : ℚ) : WithTop ℚ) < (↑delta : WithTop ℚ) := by
    rw [hdelta_coe]
    exact hDpos
  have hdelta : 0 < delta := WithTop.coe_lt_coe.mp hdelta_top
  have hb2 : (↑delta : WithTop ℚ) ≤ S.normal2.1.orderTop := by
    change (↑delta : WithTop ℚ) ≤ o2
    rw [hdelta_coe]
    exact hD2
  have hb1 : (↑delta : WithTop ℚ) ≤ S.normal1.1.orderTop := by
    change (↑delta : WithTop ℚ) ≤ o1
    rw [hdelta_coe]
    exact hD1
  have hb0 : (↑delta : WithTop ℚ) ≤ S.normal0.1.orderTop := by
    change (↑delta : WithTop ℚ) ≤ o0
    rw [hdelta_coe]
    exact hD0
  let Xn := GCD369CubeHahnRegular.shift S.normal2 delta hb2
  let Yn := GCD369CubeHahnRegular.shift S.normal1 delta hb1
  let Zn := GCD369CubeHahnRegular.shift S.normal0 delta hb0
  refine {
    delta := delta
    hdelta := hdelta
    Xn := Xn
    Yn := Yn
    Zn := Zn
    hnormal2 := ?_
    hnormal1 := ?_
    hnormal0 := ?_
    hleading := ?_
  }
  · exact (GCD369CubeHahnRegular.monomial_mul_shift
      S.normal2 delta hdelta.le hb2).symm
  · exact (GCD369CubeHahnRegular.monomial_mul_shift
      S.normal1 delta hdelta.le hb1).symm
  · exact (GCD369CubeHahnRegular.monomial_mul_shift
      S.normal0 delta hdelta.le hb0).symm
  · have hchoice : D = o2 ∨ D = o1 ∨ D = o0 := by
      rcases min_choice (min o2 o1) o0 with hout | hout
      · rcases min_choice o2 o1 with hin | hin
        · exact Or.inl (by simpa only [D] using hout.trans hin)
        · exact Or.inr (Or.inl (by simpa only [D] using hout.trans hin))
      · exact Or.inr (Or.inr (by simpa only [D] using hout))
    rcases hchoice with h2 | h1 | h0
    · left
      have horder : S.normal2.1.orderTop = (↑delta : WithTop ℚ) := by
        change o2 = (↑delta : WithTop ℚ)
        exact (hdelta_coe.trans h2).symm
      simpa only [Xn] using
        (GCD369CubeHahnRegular.constantCoeff_shift_ne_zero
          S.normal2 delta horder)
    · right; left
      have horder : S.normal1.1.orderTop = (↑delta : WithTop ℚ) := by
        change o1 = (↑delta : WithTop ℚ)
        exact (hdelta_coe.trans h1).symm
      simpa only [Yn] using
        (GCD369CubeHahnRegular.constantCoeff_shift_ne_zero
          S.normal1 delta horder)
    · right; right
      have horder : S.normal0.1.orderTop = (↑delta : WithTop ℚ) := by
        change o0 = (↑delta : WithTop ℚ)
        exact (hdelta_coe.trans h0).symm
      simpa only [Zn] using
        (GCD369CubeHahnRegular.constantCoeff_shift_ne_zero
          S.normal0 delta horder)

/-- The ninth Faber value along the canonical transverse scale is the cubic
value cubed, plus its first common-normal coupling, plus an error divisible
by the square of the transverse monomial. -/
theorem TransverseScale.faberNineExpansion
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    ∃ E : GCD369CubeHahnRegular k,
      GCD369CubeFaberNineValueQ GCD369CubeHahnRegular.ratCast
          S.normal.sextic.scale.regular0
          S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2
          S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4
          S.normal.sextic.regularX =
        S.cubicValue ^ 3 +
          GCD369CubeHahnRegular.ratCast (3 / 2) *
            S.cubicValue * S.transverseValue +
          (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 * E := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have ha4 : S.normal.sextic.scale.regular4 = 2 * S.cubicU :=
    S.regular4_eq_two_cubicU
  have ha3 : S.normal.sextic.scale.regular3 = 2 * S.cubicV :=
    S.regular3_eq_two_cubicV
  have ha2 : S.normal.sextic.scale.regular2 =
      S.cubicU ^ 2 + T.Xn * H := by
    have hn2 := T.hnormal2
    dsimp only [normal2] at hn2
    dsimp only [H]
    linear_combination hn2
  have ha1 : S.normal.sextic.scale.regular1 =
      2 * S.cubicU * S.cubicV + T.Yn * H := by
    have hn1 := T.hnormal1
    dsimp only [normal1] at hn1
    dsimp only [H]
    linear_combination hn1
  have ha0 : S.normal.sextic.scale.regular0 =
      S.cubicV ^ 2 + T.Zn * H := by
    have hn0 := T.hnormal0
    dsimp only [normal0] at hn0
    dsimp only [H]
    linear_combination hn0
  have htransverse : S.transverseValue =
      H * (T.Xn * S.normal.sextic.regularX ^ 2 +
        T.Yn * S.normal.sextic.regularX + T.Zn) := by
    dsimp only [transverseValue]
    rw [T.hnormal2, T.hnormal1, T.hnormal0]
    dsimp only [H]
    ring
  obtain ⟨Ep, hEp⟩ :=
    GCD369CubeFaberNineCommonNormalExpansionQ
      GCD369CubeHahnRegular.ratCast T.Xn T.Yn T.Zn
      S.cubicU S.cubicV S.normal.sextic.regularX
  let E : GCD369CubeHahnRegular k := Ep.eval H
  refine ⟨E, ?_⟩
  have hev := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hEp
  simp only [GCD369CubeFaberNineValueQ, RingHom.comp_apply,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at hev
  rw [ha0, ha1, ha2, ha3, ha4]
  dsimp only [cubicValue, E]
  rw [htransverse]
  dsimp only [GCD369CubeFaberNineValueQ]
  linear_combination hev

/-- Exact first zero-high numerator identity at the normalized transverse
Hahn scale. -/
theorem TransverseScale.zeroHighN1Expansion
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    729 * GCD369CubeFaberN1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (-32 * GCD369CubeNormalRow1 T.Xn T.Yn T.Zn S.cubicU) *
        (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn S.cubicU S.cubicV).1
  have h := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hp
  simp only [GCD369CubeFaberN1, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    S.regular3_eq_two_cubicV, S.regular4_eq_two_cubicU]
  simpa only [H, GCD369CubeFaberN1] using h

/-- Exact second zero-high numerator identity at the normalized transverse
Hahn scale. -/
theorem TransverseScale.zeroHighN2Expansion
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    2187 * GCD369CubeFaberN2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (32 * GCD369CubeNormalRow2
        T.Xn T.Yn T.Zn S.cubicU S.cubicV) *
        (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn S.cubicU S.cubicV).2.1
  have h := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hp
  simp only [GCD369CubeFaberN2, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    S.regular3_eq_two_cubicV, S.regular4_eq_two_cubicU]
  simpa only [H, GCD369CubeFaberN2] using h

/-- Exact third zero-high numerator identity; its remainder is an explicit
regular cubic-order term. -/
theorem TransverseScale.zeroHighN3Expansion
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (128 * GCD369CubeNormalRow3
        T.Xn T.Yn T.Zn S.cubicU S.cubicV) *
          (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 -
        (64 * T.Xn ^ 3) *
          (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 3 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn S.cubicU S.cubicV).2.2.1
  have h := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hp
  simp only [GCD369CubeFaberN3, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    S.regular3_eq_two_cubicV, S.regular4_eq_two_cubicU]
  simpa only [H, GCD369CubeFaberN3] using h

/-- Exact fourth zero-high numerator identity; its remainder is an explicit
regular cubic-order term. -/
theorem TransverseScale.zeroHighN4Expansion
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    6561 * GCD369CubeFaberN4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (32 * GCD369CubeNormalRow4
        T.Xn T.Yn T.Zn S.cubicU S.cubicV) *
          (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 -
        (314928 * T.Yn * T.Xn ^ 2) *
          (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 3 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn S.cubicU S.cubicV).2.2.2
  have h := congrArg (Polynomial.evalRingHom H) hp
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat,
    GCD369CubeFaberN4_map, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    S.regular3_eq_two_cubicV, S.regular4_eq_two_cubicU]
  simpa only [H] using h

/-- The recovered residue is a root of the certified limiting common cubic. -/
theorem leadingCubicRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let r := S.normal.sextic.scaledX.coeff 0
    r ^ 3 + S.u * r + S.v = 0 := by
  dsimp only
  have hf := S.normal.sextic.leadingSexticRoot
  rw [S.ha4, S.ha3, S.ha2, S.ha1, S.ha0] at hf
  have hsquare :
      (S.normal.sextic.scaledX.coeff 0 ^ 3 +
        S.u * S.normal.sextic.scaledX.coeff 0 + S.v) ^ 2 = 0 := by
    linear_combination hf
  exact (sq_eq_zero_iff).mp hsquare

/-- The scaled sextic value is exactly the moving cubic square plus its
transverse quadratic value. -/
theorem commonNormalEquation
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    S.cubicValue ^ 2 + S.transverseValue =
      S.normal.sextic.scale.weightedRegular 6 S.normal.sextic.value := by
  have hhalf :
      (2 : GCD369CubeHahnRegular k) *
        GCD369CubeHahnRegular.ratCast (1 / 2) = 1 := by
    have htwo : (2 : GCD369CubeHahnRegular k) =
        GCD369CubeHahnRegular.constant (2 : k) := by
      apply Subtype.ext
      exact (map_ofNat (HahnSeries.C : k →+* HahnSeries ℚ k) 2).symm
    have hrat : GCD369CubeHahnRegular.ratCast (1 / 2) =
        GCD369CubeHahnRegular.constant (1 / 2 : k) := by
      change GCD369CubeHahnRegular.constant (algebraMap ℚ k (1 / 2)) =
        GCD369CubeHahnRegular.constant (1 / 2 : k)
      congr 1
      norm_num
    calc
      _ = GCD369CubeHahnRegular.constant (2 : k) *
          GCD369CubeHahnRegular.constant (1 / 2 : k) := by rw [htwo, hrat]
      _ = GCD369CubeHahnRegular.constant ((2 : k) * (1 / 2 : k)) :=
        ((GCD369CubeHahnRegular.constant (k := k)).map_mul _ _).symm
      _ = 1 := by norm_num
  have ha4 : S.normal.sextic.scale.regular4 = 2 * S.cubicU := by
    dsimp only [cubicU]
    linear_combination
      -S.normal.sextic.scale.regular4 * hhalf
  have ha3 : S.normal.sextic.scale.regular3 = 2 * S.cubicV := by
    dsimp only [cubicV]
    linear_combination
      -S.normal.sextic.scale.regular3 * hhalf
  have hscaled :
      S.normal.sextic.regularX ^ 6 +
        (S.normal.sextic.scale.regular4 * S.normal.sextic.regularX ^ 4 +
          (S.normal.sextic.scale.regular3 * S.normal.sextic.regularX ^ 3 +
            (S.normal.sextic.scale.regular2 * S.normal.sextic.regularX ^ 2 +
              (S.normal.sextic.scale.regular1 * S.normal.sextic.regularX +
                S.normal.sextic.scale.regular0)))) =
        S.normal.sextic.scale.weightedRegular 6 S.normal.sextic.value := by
    apply Subtype.ext
    exact S.normal.sextic.scaledEquation
  rw [ha4, ha3] at hscaled
  dsimp only [cubicValue, transverseValue, normal2, normal1, normal0]
  linear_combination hscaled

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- The literal finite pole canonically supplies the complete moving
common-cubic normal-coordinate packet. -/
noncomputable def finiteCommonValueData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnCommonValueData k := by
  let N := S.finiteNormalValueData a hpole
  let hex := S.finiteLeadingComponent_common a hpole
  let u := Classical.choose hex
  let hu := Classical.choose_spec hex
  let v := Classical.choose hu
  let hv := Classical.choose_spec hu
  refine {
    normal := N
    u := u
    v := v
    hprojective := hv.1
    ha4 := ?_
    ha3 := ?_
    ha2 := ?_
    ha1 := ?_
    ha0 := ?_
  }
  · exact hv.2.1
  · exact hv.2.2.1
  · exact hv.2.2.2.1
  · exact hv.2.2.2.2.1
  · exact hv.2.2.2.2.2

/-- At every finite pole selected from the literal source, the recovered
translation residue is a root of the nonzero common cubic supplied by the
leading Faber component. -/
theorem finiteLeadingCommonCubicRoot
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    let B := S.finiteSexticValueData a hpole
    let r := B.scaledX.coeff 0
    ∃ u v : k, (u ≠ 0 ∨ v ≠ 0) ∧
      B.scale.leading4 = 2 * u ∧
      B.scale.leading3 = 2 * v ∧
      B.scale.leading2 = u ^ 2 ∧
      B.scale.leading1 = 2 * u * v ∧
      B.scale.leading0 = v ^ 2 ∧
      r ^ 3 + u * r + v = 0 := by
  let B := S.finiteSexticValueData a hpole
  let r := B.scaledX.coeff 0
  obtain ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0⟩ :=
    S.finiteLeadingComponent_common a hpole
  have hf := B.leadingSexticRoot
  change r ^ 6 +
      (B.scale.leading4 * r ^ 4 +
        (B.scale.leading3 * r ^ 3 +
          (B.scale.leading2 * r ^ 2 +
            (B.scale.leading1 * r + B.scale.leading0)))) = 0 at hf
  have hsquare : (r ^ 3 + u * r + v) ^ 2 = 0 := by
    rw [ha4, ha3, ha2, ha1, ha0] at hf
    linear_combination hf
  exact ⟨u, v, hprojective, ha4, ha3, ha2, ha1, ha0,
    (sq_eq_zero_iff).mp hsquare⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubeZeroLoadNormal_parametrization
#print axioms GCD369CubeZeroLoadNormal_commonRoot
#print axioms GCD369CubeZeroLoadNormal_factorization
#print axioms GCD369CubeFaberNineCommonNormalExpansionQ
#print axioms GCD369CubeFaberCommonNormalNumeratorsCommRing
#print axioms GCD369CubeFaberN4_map
#print axioms GCD369CubeHahnRegular.two_mul_ratCast_half
#print axioms GCD369CubeHahnRegular.orderTop_pos_of_constantCoeff_zero
#print axioms GCD369CubeHahnRegular.monomial_mul_shift
#print axioms GCD369CubeHahnRegular.constantCoeff_shift
#print axioms GCD369CubeHahnRegular.constantCoeff_shift_ne_zero
#print axioms GCD369CubeHahnRegular.coeff_eq_zero_of_neg
#print axioms GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
#print axioms GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
#print axioms GCD369CubeHahnCommonValueData.normal_constantCoeff_zero
#print axioms GCD369CubeHahnCommonValueData.transverseScale
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.faberNineExpansion
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.zeroHighN1Expansion
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.zeroHighN2Expansion
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.zeroHighN3Expansion
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.zeroHighN4Expansion
#print axioms GCD369CubeHahnCommonValueData.leadingCubicRoot
#print axioms GCD369CubeHahnCommonValueData.commonNormalEquation
#print axioms GCD369CubePolynomialSource.finiteCommonValueData
#print axioms GCD369CubePolynomialSource.finiteLeadingCommonCubicRoot
