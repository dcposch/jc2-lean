import FiniteDoubleHahn

/-! # The second double-root blowup

The first surviving zero-load normal is the double-root direction
`A * (1, r, -2*r^2)`.  This file records the exact change of variables at
that point.  Its linear kernel has one residual direction, and the quadratic
third and fourth rows obstruct that direction at the half scale.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- A regular Hahn series with nonzero residue has a regular inverse. -/
noncomputable def invOfConstantCoeffNe
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (hx : constantCoeff x ≠ 0) : GCD369CubeHahnRegular k := by
  have hxcoeff : x.1.coeff 0 ≠ 0 := hx
  have hxne : x.1 ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hxcoeff
  have hxorder : x.1.order = 0 := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero hxcoeff
    · exact HahnSeries.zero_le_orderTop_iff.mp x.2
  have hinvorder : x.1⁻¹.order = -x.1.order := by
    have hmul := HahnSeries.order_mul (inv_ne_zero hxne) hxne
    rw [inv_mul_cancel₀ hxne, HahnSeries.order_one] at hmul
    linarith
  refine ⟨x.1⁻¹, ?_⟩
  change (↑(0 : ℚ) : WithTop ℚ) ≤ x.1⁻¹.orderTop
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero (inv_ne_zero hxne),
    hinvorder, hxorder]
  simp

/-- The constructed regular inverse is a right inverse in the local ring. -/
theorem mul_invOfConstantCoeffNe
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (hx : constantCoeff x ≠ 0) :
    x * invOfConstantCoeffNe x hx = 1 := by
  apply Subtype.ext
  exact mul_inv_cancel₀ (HahnSeries.ne_zero_of_coeff_ne_zero hx)

/-- Its residue is the inverse of the original residue. -/
theorem constantCoeff_invOfConstantCoeffNe
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (hx : constantCoeff x ≠ 0) :
    constantCoeff (invOfConstantCoeffNe x hx) = (constantCoeff x)⁻¹ := by
  have h := congrArg constantCoeff (mul_invOfConstantCoeffNe x hx)
  have h' : constantCoeff x *
      constantCoeff (invOfConstantCoeffNe x hx) = 1 := by
    simpa only [map_mul, map_one] using h
  exact eq_inv_of_mul_eq_one_right h'

/-- The canonical moving root determined by a unit quadratic coefficient
`U` and the cubic coefficient `V`. -/
noncomputable def movingDoubleRoot
    {k : Type*} [Field k] [CharZero k]
    (U V : GCD369CubeHahnRegular k) (hU : constantCoeff U ≠ 0) :
    GCD369CubeHahnRegular k :=
  ratCast (-3 / 2) * V * invOfConstantCoeffNe U hU

/-- By construction the moving root satisfies `2*U*r + 3*V = 0`. -/
theorem movingDoubleRoot_relation
    {k : Type*} [Field k] [CharZero k]
    (U V : GCD369CubeHahnRegular k) (hU : constantCoeff U ≠ 0) :
    2 * U * movingDoubleRoot U V hU + 3 * V = 0 := by
  have hinv := mul_invOfConstantCoeffNe U hU
  have hscalar :
      (2 : GCD369CubeHahnRegular k) * ratCast (-3 / 2) = -3 := by
    calc
      (2 : GCD369CubeHahnRegular k) * ratCast (-3 / 2) =
          ratCast 2 * ratCast (-3 / 2) := by rw [map_ofNat]
      _ = ratCast (2 * (-3 / 2)) := (map_mul _ _ _).symm
      _ = ratCast (-3) := by norm_num
      _ = -3 := by rw [map_neg, map_ofNat]
  dsimp only [movingDoubleRoot]
  calc
    _ = (2 * ratCast (-3 / 2)) *
        (U * invOfConstantCoeffNe U hU) * V + 3 * V := by ring
    _ = 0 := by rw [hscalar, hinv]; ring

/-- At a double-root residue, the canonical moving root has the expected
residue. -/
theorem constantCoeff_movingDoubleRoot
    {k : Type*} [Field k] [CharZero k]
    (U V : GCD369CubeHahnRegular k) (hU : constantCoeff U ≠ 0)
    (r : k) (hUr : constantCoeff U = -3 * r ^ 2)
    (hVr : constantCoeff V = 2 * r ^ 3) (hr : r ≠ 0) :
    constantCoeff (movingDoubleRoot U V hU) = r := by
  simp only [movingDoubleRoot, map_mul,
    constantCoeff_invOfConstantCoeffNe, constantCoeff_ratCast]
  rw [hUr, hVr]
  field_simp [hr]
  have hscalar : algebraMap ℚ k (-(3 / 2)) * 2 = -3 := by
    calc
      algebraMap ℚ k (-(3 / 2)) * 2 =
          algebraMap ℚ k (-(3 / 2)) * algebraMap ℚ k 2 := by rw [map_ofNat]
      _ = algebraMap ℚ k ((-(3 / 2)) * 2) := (map_mul _ _ _).symm
      _ = -3 := by norm_num
  rw [hscalar]
  norm_num

/-- Multiplication by a positive Hahn monomial power translates every
coefficient, not only the constant coefficient. -/
theorem coeff_mul_monomial_pow_add
    {k : Type*} [Field k] (x : GCD369CubeHahnRegular k)
    (delta q : ℚ) (hdelta : 0 ≤ delta) (n : ℕ) :
    (x * (monomial delta hdelta) ^ n).1.coeff
        (q + (n : ℚ) * delta) = x.1.coeff q := by
  change (x.1 * (HahnSeries.single delta (1 : k)) ^ n).coeff
      (q + (n : ℚ) * delta) = x.1.coeff q
  rw [HahnSeries.single_pow]
  simpa only [nsmul_eq_mul, one_pow, mul_one] using
    (HahnSeries.coeff_mul_single_add
      (x := x.1) (r := (1 : k)) (a := q) (b := (n : ℕ) • delta))

end GCD369CubeHahnRegular

/-- Exact first normal row after moving the double root and separating the
three deviations `B`, `C`, and `d`. -/
theorem GCD369CubeDoubleBlowupRow1
    {R : Type*} [CommRing R] (A B C r d : R) :
    GCD369CubeNormalRow1 A (r * A + B) (-2 * r ^ 2 * A + C)
        (-3 * r ^ 2 + d) =
      729 * (A ^ 2 * d - 2 * A * B * r - B ^ 2 - 2 * A * C) := by
  simp only [GCD369CubeNormalRow1]
  ring

/-- Exact second row in the moving double-root chart.  The equation on `e`
is the identity `2*u*r + 3*v = 0` used to choose the moving root. -/
theorem GCD369CubeDoubleBlowupRow2
    {R : Type*} [CommRing R] (A B C r d e : R)
    (hre : 3 * e + 2 * d * r = 0) :
    GCD369CubeNormalRow2 A (r * A + B) (-2 * r ^ 2 * A + C)
        (-3 * r ^ 2 + d) (2 * r ^ 3 + e) =
      -1458 * (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
        3 * A * C * r + 3 * A * B * d - 3 * B * C) := by
  simp only [GCD369CubeNormalRow2]
  linear_combination -729 * A ^ 2 * hre

/-- Exact third row in the moving double-root chart. -/
theorem GCD369CubeDoubleBlowupRow3
    {R : Type*} [CommRing R] (A B C r d e : R)
    (hre : 3 * e + 2 * d * r = 0) :
    GCD369CubeNormalRow3 A (r * A + B) (-2 * r ^ 2 * A + C)
        (-3 * r ^ 2 + d) (2 * r ^ 3 + e) =
      -2 * A ^ 2 * r ^ 2 * d + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * d ^ 2 - 2 * B ^ 2 * d - 4 * A * C * d +
        3 * C ^ 2 := by
  simp only [GCD369CubeNormalRow3]
  linear_combination -2 * A * (A * r + B) * hre

/-- Exact fourth row in the moving double-root chart. -/
theorem GCD369CubeDoubleBlowupRow4
    {R : Type*} [CommRing R] (A B C r d e : R)
    (hre : 3 * e + 2 * d * r = 0) :
    GCD369CubeNormalRow4 A (r * A + B) (-2 * r ^ 2 * A + C)
        (-3 * r ^ 2 + d) (2 * r ^ 3 + e) =
      4374 * (-3 * r ^ 2 + d) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * d - 3 * B * C) := by
  simp only [GCD369CubeNormalRow4]
  linear_combination
    (-6561 * A ^ 2 * r ^ 2 - 8748 * A * B * r + 6561 * A ^ 2 * d -
      4374 * B ^ 2 - 8748 * A * C) * hre

/-- The linearized first two rows have a one-dimensional kernel.  The
moving-discriminant deviation vanishes and `C = -r*B`. -/
theorem GCD369CubeDoubleBlowup_linearKernel
    {K : Type*} [Field K] [CharZero K]
    (A B C r d : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 : A ^ 2 * d - 2 * A * B * r - 2 * A * C = 0)
    (h2 : 2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
      3 * A * C * r = 0) :
    d = 0 ∧ C = -r * B := by
  have hdprod : A ^ 2 * r * d = 0 := by
    linear_combination 2 * h2 - 3 * r * h1
  have hd : d = 0 := by
    rcases mul_eq_zero.mp hdprod with hAr | hd
    · rcases mul_eq_zero.mp hAr with hA2 | hr0
      · exact (hA (sq_eq_zero_iff.mp hA2)).elim
      · exact (hr hr0).elim
    · exact hd
  constructor
  · exact hd
  · rw [hd] at h1
    have hAC : A * (C + r * B) = 0 := by
      linear_combination (-1 / 2) * h1
    have hsum : C + r * B = 0 :=
      (mul_eq_zero.mp hAC).resolve_left hA
    linear_combination hsum

/-- On the residual linear-kernel direction the quadratic third row is
`9*r^2*B^2`. -/
theorem GCD369CubeDoubleBlowup_row3_onKernel
    {R : Type*} [CommRing R] (B r : R) :
    6 * B ^ 2 * r ^ 2 + 3 * (-r * B) ^ 2 =
      9 * r ^ 2 * B ^ 2 := by
  ring

/-- On the same direction the quadratic fourth row is
`-65610*r^3*B^2`. -/
theorem GCD369CubeDoubleBlowup_row4_onKernel
    {R : Type*} [CommRing R] (A B r : R) :
    4374 * (-3 * r ^ 2) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * (-r * B) * r -
          3 * B * (-r * B)) =
      -65610 * r ^ 3 * B ^ 2 := by
  ring

/-- The next coefficients in rows one and two determine the moving-
discriminant correction.  After eliminating the otherwise arbitrary second
correction `Q`, the third row is exactly `27*r^2*B^2` and the fourth row
vanishes.  This is the coordinate-free content of the complete cubic-row
calculation at the double root. -/
theorem GCD369CubeDoubleBlowup_secondCorrection
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d : K) (hr : r ≠ 0)
    (h1 : A ^ 2 * d - 2 * A * Q - B ^ 2 = 0)
    (h2 : 2 * A ^ 2 * r * d - 3 * A * r * Q +
      3 * r * B ^ 2 = 0) :
    (-2 * A ^ 2 * r ^ 2 * d + 9 * r ^ 2 * B ^ 2 =
        27 * r ^ 2 * B ^ 2) ∧
      (-13122 * A * r ^ 3 * Q - 65610 * r ^ 3 * B ^ 2 = 0) := by
  have hdr : A ^ 2 * r * d + 9 * r * B ^ 2 = 0 := by
    linear_combination 2 * h2 - 3 * r * h1
  have hd : A ^ 2 * d + 9 * B ^ 2 = 0 := by
    have hfac : r * (A ^ 2 * d + 9 * B ^ 2) = 0 := by
      linear_combination hdr
    exact (mul_eq_zero.mp hfac).resolve_left hr
  have hQ : A * Q + 5 * B ^ 2 = 0 := by
    linear_combination (-1 / 2) * (h1 - hd)
  constructor
  · linear_combination (-2 * r ^ 2) * hd
  · linear_combination (-13122 * r ^ 3) * hQ

/-- At the resonant half scale, rows one and two make the row-four normal
contribution vanish, leaving its nonzero cubic remainder. -/
theorem GCD369CubeDoubleBlowup_correctedHalfScale_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B Q r d : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 : A ^ 2 * d - 2 * A * Q - B ^ 2 = 0)
    (h2 : 2 * A ^ 2 * r * d - 3 * A * r * Q +
      3 * r * B ^ 2 = 0)
    (h4 : 32 * (-13122 * A * r ^ 3 * Q -
      65610 * r ^ 3 * B ^ 2) - 314928 * (r * A) * A ^ 2 = 0) : False := by
  have hz := (GCD369CubeDoubleBlowup_secondCorrection
    A B Q r d hr h1 h2).2
  rw [hz] at h4
  norm_num at h4
  rcases h4 with hr0 | hA0
  · exact hr hr0
  · exact hA hA0

/-- At the resonant half scale, the cubic remainders in rows three and four
are incompatible with the unique residual tangent direction. -/
theorem GCD369CubeDoubleBlowup_halfScale_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A B r : K) (hB : B ≠ 0) (hr : r ≠ 0)
    (h3 : 128 * (9 * r ^ 2 * B ^ 2) - 64 * A ^ 3 = 0)
    (h4 : 32 * (-65610 * r ^ 3 * B ^ 2) -
      314928 * (r * A) * A ^ 2 = 0) : False := by
  have hprod : (-7768224 : K) * r ^ 3 * B ^ 2 = 0 := by
    linear_combination h4 - (19683 / 4 * r) * h3
  rcases mul_eq_zero.mp hprod with hr3 | hB2
  · norm_num at hr3
    exact hr hr3
  · exact hB (sq_eq_zero_iff.mp hB2)

#print axioms GCD369CubeDoubleBlowupRow1
#print axioms GCD369CubeDoubleBlowupRow2
#print axioms GCD369CubeDoubleBlowupRow3
#print axioms GCD369CubeDoubleBlowupRow4
#print axioms GCD369CubeDoubleBlowup_linearKernel
#print axioms GCD369CubeDoubleBlowup_secondCorrection
#print axioms GCD369CubeDoubleBlowup_correctedHalfScale_inconsistent
#print axioms GCD369CubeDoubleBlowup_halfScale_inconsistent
