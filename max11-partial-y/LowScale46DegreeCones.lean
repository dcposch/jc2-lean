import LowScale46AlignedChart

/-! # Finite degree cones in the `(4,6)` polynomial endgame

This module replaces the source report's finite integer scans by exact
Presburger proofs.  `MaxTie4` says that the maximum of four candidate degrees
is attained at least twice.  Applying it to the two coefficient-curve rows
gives the unique positive mismatch cone `(4n,5n,7n)`; the two aligned cones
are solved exactly as well.
-/

namespace Max11DegreeRoutes

/-- Among four natural numbers, the maximum is attained at least twice. -/
def MaxTie4 (a b c d : ℕ) : Prop :=
  (a = b ∧ c ≤ a ∧ d ≤ a) ∨
  (a = c ∧ b ≤ a ∧ d ≤ a) ∨
  (a = d ∧ b ≤ a ∧ c ≤ a) ∨
  (b = c ∧ a ≤ b ∧ d ≤ b) ∨
  (b = d ∧ a ≤ b ∧ c ≤ b) ∨
  (c = d ∧ a ≤ c ∧ b ≤ c)

/-- The two mismatch leading supports have the unique positive primitive
degree cone `(deg A,deg B,deg U)=(4n,5n,7n)`. -/
theorem mismatchDegreeCone46
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hJ2 : MaxTie4 (3 * a) (a + u) (2 * b) (b + u))
    (hJ1 : MaxTie4 (2 * a + b) (a + 2 * b) (b + u) (2 * u)) :
    ∃ n : ℕ, 0 < n ∧ a = 4 * n ∧ b = 5 * n ∧ u = 7 * n := by
  have hratio : 5 * a = 4 * b ∧ 7 * a = 4 * u := by
    rcases hJ2 with h12 | h13 | h14 | h23 | h24 | h34 <;>
      rcases hJ1 with k12 | k13 | k14 | k23 | k24 | k34 <;>
      omega
  rcases hratio with ⟨hab, hau⟩
  have h4mul : 4 ∣ a * 5 := by
    refine ⟨b, ?_⟩
    omega
  have h4a : 4 ∣ a :=
    ((by norm_num : Nat.Coprime 4 5).dvd_mul_right).mp h4mul
  rcases h4a with ⟨n, hn⟩
  refine ⟨n, ?_, ?_, ?_, ?_⟩ <;> omega

/-- In the aligned `beta != 0` cone, the two leading equations force the
primitive degree ratio `(4,3,5)`. -/
theorem alignedBetaDegreeCone46
    (a x v : ℕ) (ha : 0 < a) (hx : 0 < x) (hv : 0 < v)
    (hPhi : x + v = 2 * a) (hR : 2 * v = a + 2 * x) :
    ∃ n : ℕ, 0 < n ∧ a = 4 * n ∧ x = 3 * n ∧ v = 5 * n := by
  have hratio : 3 * a = 4 * x := by omega
  have h4mul : 4 ∣ a * 3 := by
    refine ⟨x, ?_⟩
    omega
  have h4a : 4 ∣ a :=
    ((by norm_num : Nat.Coprime 4 3).dvd_mul_right).mp h4mul
  rcases h4a with ⟨n, hn⟩
  refine ⟨n, ?_, ?_, ?_, ?_⟩ <;> omega

/-- In the aligned `beta=0, delta != 0` cone, the two leading equations
force the primitive degree ratio `(4,1,3)`. -/
theorem alignedDeltaDegreeCone46
    (a x v : ℕ) (ha : 0 < a) (hx : 0 < x) (hv : 0 < v)
    (hPhi : x + v = a) (hR : 2 * v = a + 2 * x) :
    ∃ n : ℕ, 0 < n ∧ a = 4 * n ∧ x = n ∧ v = 3 * n := by
  refine ⟨x, hx, ?_, rfl, ?_⟩ <;> omega

/-- The mismatch cone's top one-form degree is strictly above every
competitor and is never zero. -/
theorem mismatchEtaDegreeGap46 (n : ℕ) (hn : 0 < n) :
    15 * n - 1 < 16 * n - 1 ∧ 0 < 16 * n - 1 := by
  omega

/-- The aligned `beta` cone's top one-form degree is strictly above the two
other shifted contributions and is never zero. -/
theorem alignedBetaEtaDegreeGap46 (n : ℕ) (hn : 0 < n) :
    9 * n - 1 < 12 * n - 1 ∧ 0 < 12 * n - 1 := by
  omega

/-- The aligned `delta` cone's top one-form degree is nonzero. -/
theorem alignedDeltaEtaDegreePositive46 (n : ℕ) (hn : 0 < n) :
    0 < 8 * n - 1 := by
  omega

section LeadingCoefficients

variable {F : Type*} [Field F] [CharZero F]

/-- The mismatch cone's two leading curve equations force the advertised
nonzero top coefficient of the pulled-back one-form. -/
theorem mismatch_leadingEtaCoefficient46
    (L a0 b0 u0 : F) (hL : L ≠ 0) (ha0 : a0 ≠ 0)
    (hlead : 5 * L * a0 ^ 3 = 24 * b0 * u0) :
    (15 / 64 : F) * L * a0 ^ 3 + (3 / 16 : F) * b0 * u0 =
        (35 / 128 : F) * L * a0 ^ 3 ∧
      (35 / 128 : F) * L * a0 ^ 3 ≠ 0 := by
  constructor
  · linear_combination (-1 / 128 : F) * hlead
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hL) (pow_ne_zero 3 ha0)

/-- The unique top coefficient when only `B,U` vary in the mismatch branch
is nonzero in characteristic zero. -/
theorem mismatch_BU_leadingEtaCoefficient46
    (n : ℕ) (hn : 0 < n) (b0 : F) (hb0 : b0 ≠ 0) :
    (-3 / 4 : F) * (n : F) * b0 ^ 3 ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'))
    (pow_ne_zero 3 hb0)

end LeadingCoefficients

end Max11DegreeRoutes
