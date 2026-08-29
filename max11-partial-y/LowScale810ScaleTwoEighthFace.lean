import LowScale810ScaleTwoSeventhPacket

/-! # Scale-two eighth face for normalized `(8,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₇ H - 4 q₉ = λ h⁹` with
`h.natDegree = 1`, the seventh-face packet supplies the degree-`10`
integral and the exact two-component root split of the sixth-face jet.
The next Keller coefficient is the degree-`9` Jacobian row already
recorded as `eighthCoefficientJacobianRow_810`.  After the same octic
depression that kills `z⁷`, that row is
`10 G' + 9 L F' + 8 P E' + 7 Q D' + 6 R C' + 5 S B' + 4 T A'
- 2 E P' - 3 D Q' - 4 C R' - 5 B S' - 6 A T' - 8 V' = 0`.  The
resulting first integral is the residual `η` below.

Evaluating the sixth defect on the sixth-face jet at the root of `h`
refines both seventh-packet components: the `v₀ = 0` branch also forces
`u₀ = w₀ = 0`, and the `t₀ = 0` branch also forces `v₀ = s₀ = b₆ = 0`.
Neither alternative is discarded.

No total-degree or twice-prime theorem is used.  The aligned face `N = 0`
is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Octic `z⁰` and decic `z²` coordinates -/

section Depression810Eighth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed octic `z⁰` coefficient. -/
def depressedG810 (h r a7 a6 a5 a4 a3 a2 a1 a0 : F) : F :=
  depressedV68 h r a7 a6 a5 a4 a3 a2 a1 a0

/-- Depressed decic `z²` coefficient. -/
def depressedV810 (h r b9 b8 b7 b6 b5 b4 b3 b2 : F) : F :=
  45 * r ^ 8 - 36 * (b9 / h ^ 9) * r ^ 7 +
    28 * (b8 / h ^ 8) * r ^ 6 - 21 * (b7 / h ^ 7) * r ^ 5 +
    15 * (b6 / h ^ 6) * r ^ 4 - 10 * (b5 / h ^ 5) * r ^ 3 +
    6 * (b4 / h ^ 4) * r ^ 2 - 3 * (b3 / h ^ 3) * r + b2 / h ^ 2

/-- First residual of the degree-`9` row. -/
def etaResidual810 (L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 : F) : F :=
  V0 - ((5 / 4 : F) * G0 + (9 / 8 : F) * L * F0 +
    alphaResidual810 A P * E0 +
    (7 / 8 : F) * betaResidual810 L A B Q * D0 +
    (3 / 4 : F) * gammaResidual810 L A B C0 P R * C0 +
    (5 / 8 : F) * deltaResidual810 L A B C0 D0 P Q S0 * B +
    (1 / 2 : F) * epsilonResidual810 L A B C0 D0 E0 P Q R T0 * A +
    (5 / 16 : F) * A * E0 + (5 / 16 : F) * B * D0 +
    (5 / 32 : F) * C0 ^ 2 - (15 / 128 : F) * A * B ^ 2 -
    (15 / 128 : F) * A ^ 2 * C0 + (35 / 2048 : F) * A ^ 4 +
    (9 / 64 : F) * L * B * C0 + (9 / 64 : F) * L * A * D0 -
    (63 / 1024 : F) * L * A ^ 2 * B -
    (7 / 64 : F) * betaResidual810 L A B Q * A * B -
    (3 / 32 : F) * gammaResidual810 L A B C0 P R * A ^ 2)

theorem coeff_depressedOctic68_zero
    (L P Q R S T0 U V : F) :
    (depressedOctic68 L P Q R S T0 U V).coeff 0 = V := by
  simp [depressedOctic68, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
    coeff_X]

/-- Exact denominator clearing for the octic `z⁰` coordinate. -/
theorem depressedG810_eq_cleared
    (h a7 a6 a5 a4 a3 a2 a1 a0 : F) (hh : h ≠ 0) :
    depressedG810 h (octicDepressionR810 h a7) a7 a6 a5 a4 a3 a2 a1 a0 =
      (16777216 * a0 * h ^ 56 - 2097152 * a1 * a7 * h ^ 48 +
          262144 * a2 * a7 ^ 2 * h ^ 40 - 32768 * a3 * a7 ^ 3 * h ^ 32 +
          4096 * a4 * a7 ^ 4 * h ^ 24 - 512 * a5 * a7 ^ 5 * h ^ 16 +
          64 * a6 * a7 ^ 6 * h ^ 8 - 7 * a7 ^ 8) /
        (16777216 * h ^ 56) := by
  simp only [depressedG810, depressedV68, octicDepressionR810]
  field_simp [hh]
  ring

/-- Exact denominator clearing for the decic `z²` coordinate on the
ninth-power face. -/
theorem depressedV810_eq_cleared
    (h a7 b9 b8 b7 b6 b5 b4 b3 b2 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a7 * h ^ 2 - 4 * b9 = lambda * h ^ 9) :
    depressedV810 h (octicDepressionR810 h a7) b9 b8 b7 b6 b5 b4 b3 b2 =
      (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
          1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
          61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
          1572864 * a7 ^ 2 * b4 * h ^ 38 - 6291456 * a7 * b3 * h ^ 46 +
          16777216 * b2 * h ^ 54) /
        (16777216 * h ^ 56) := by
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4pow : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hb9 : 4 * b9 = 5 * a7 * h ^ 2 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedV810, octicDepressionR810]
  have hrewrite :
      45 * (a7 / (8 * h ^ 7)) ^ 8 -
          36 * (b9 / h ^ 9) * (a7 / (8 * h ^ 7)) ^ 7 +
        28 * (b8 / h ^ 8) * (a7 / (8 * h ^ 7)) ^ 6 -
          21 * (b7 / h ^ 7) * (a7 / (8 * h ^ 7)) ^ 5 +
        15 * (b6 / h ^ 6) * (a7 / (8 * h ^ 7)) ^ 4 -
          10 * (b5 / h ^ 5) * (a7 / (8 * h ^ 7)) ^ 3 +
        6 * (b4 / h ^ 4) * (a7 / (8 * h ^ 7)) ^ 2 -
          3 * (b3 / h ^ 3) * (a7 / (8 * h ^ 7)) + b2 / h ^ 2 =
        (-315 * a7 ^ 8 + 72 * lambda * a7 ^ 7 * h ^ 7 +
            1792 * a7 ^ 6 * b8 * h ^ 6 - 10752 * a7 ^ 5 * b7 * h ^ 14 +
            61440 * a7 ^ 4 * b6 * h ^ 22 - 327680 * a7 ^ 3 * b5 * h ^ 30 +
            1572864 * a7 ^ 2 * b4 * h ^ 38 - 6291456 * a7 * b3 * h ^ 46 +
            16777216 * b2 * h ^ 54) /
          (16777216 * h ^ 56) := by
    field_simp [hh, h8, h4, hh2, hh3, hh4pow, hh5, hh6, hh7, hh8pow, hh9,
      hh56, h16777216]
    have hb9' :
        b9 = (5 * a7 * h ^ 2 - lambda * h ^ 9) / 4 := by
      field_simp [h4]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h8, h4, hh2, hh3, hh4pow, hh5, hh6, hh7, hh8pow, hh9,
      hh56, h16777216]
    ring
  exact hrewrite

end Depression810Eighth

/-! ## Degree-`9` depressed Jacobian coefficient -/

section DepressedRow810Eighth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic octic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`9` Jacobian coefficient is
exactly `10 G' + 9 L F' + 8 P E' + 7 Q D' + 6 R C' + 5 S B' + 4 T A'
- 2 E P' - 3 D Q' - 4 C R' - 5 B S' - 6 A T' - 8 V'`. -/
theorem differentialJacobian_coeff_9_monicOcticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 9 =
      (10 : F) * d (f.coeff 0) + (9 : F) * g.coeff 9 * d (f.coeff 1) +
        (8 : F) * g.coeff 8 * d (f.coeff 2) +
        (7 : F) * g.coeff 7 * d (f.coeff 3) +
        (6 : F) * g.coeff 6 * d (f.coeff 4) +
        (5 : F) * g.coeff 5 * d (f.coeff 5) +
        (4 : F) * g.coeff 4 * d (f.coeff 6) -
          (2 : F) * f.coeff 2 * d (g.coeff 8) -
          (3 : F) * f.coeff 3 * d (g.coeff 7) -
          (4 : F) * f.coeff 4 * d (g.coeff 6) -
          (5 : F) * f.coeff 5 * d (g.coeff 5) -
          (6 : F) * f.coeff 6 * d (g.coeff 4) -
          (8 : F) * d (g.coeff 2) := by
  have hfd_high : ∀ n, 7 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf7]
    · have : 8 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq8 | hlt8
      · subst n
        simpa [hf8, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 8 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 8 < n + 1 := by omega
    simp [hf_high (n + 1) this]
  have hgd'_high : ∀ n, 9 ≤ n → (coefficientDeriv d g).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      exact hL
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq10 | hlt10
      · subst n
        simpa [hg10, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hg_high n (by omega))
  have hmem09 : ((0, 9) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem18 : ((1, 8) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem27 : ((2, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem36 : ((3, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem45 : ((4, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem54 : ((5, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem63 : ((6, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem72 : ((7, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 9 =
        (10 : F) * d (f.coeff 0) +
          (9 : F) * g.coeff 9 * d (f.coeff 1) +
          (8 : F) * g.coeff 8 * d (f.coeff 2) +
          (7 : F) * g.coeff 7 * d (f.coeff 3) +
          (6 : F) * g.coeff 6 * d (f.coeff 4) +
          (5 : F) * g.coeff 5 * d (f.coeff 5) +
          (4 : F) * g.coeff 4 * d (f.coeff 6) := by
    rw [Polynomial.coeff_mul]
    have hne09_18 : ((0, 9) : ℕ × ℕ) ≠ (1, 8) := by decide
    have hne09_27 : ((0, 9) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne09_36 : ((0, 9) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne09_45 : ((0, 9) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne09_54 : ((0, 9) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne09_63 : ((0, 9) : ℕ × ℕ) ≠ (6, 3) := by decide
    have hne18_27 : ((1, 8) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne18_36 : ((1, 8) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne18_45 : ((1, 8) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne18_54 : ((1, 8) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne18_63 : ((1, 8) : ℕ × ℕ) ≠ (6, 3) := by decide
    have hne27_36 : ((2, 7) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne27_45 : ((2, 7) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne27_54 : ((2, 7) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne27_63 : ((2, 7) : ℕ × ℕ) ≠ (6, 3) := by decide
    have hne36_45 : ((3, 6) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne36_54 : ((3, 6) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne36_63 : ((3, 6) : ℕ × ℕ) ≠ (6, 3) := by decide
    have hne45_54 : ((4, 5) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne45_63 : ((4, 5) : ℕ × ℕ) ≠ (6, 3) := by decide
    have hne54_63 : ((5, 4) : ℕ × ℕ) ≠ (6, 3) := by decide
    have hsubset :
        ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3)} :
            Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (9 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb | hb
      · subst b; exact hmem09
      · subst b; exact hmem18
      · subst b; exact hmem27
      · subst b; exact hmem36
      · subst b; exact hmem45
      · subst b; exact hmem54
      · subst b; exact hmem63
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4),
              (6, 3)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 9 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne09 : b ≠ (0, 9) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne18 : b ≠ (1, 8) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne27 : b ≠ (2, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne36 : b ≠ (3, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne45 : b ≠ (4, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne54 : b ≠ (5, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne63 : b ≠ (6, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 7 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0; apply hne09; ext; exact h0; omega
        have hne1 : b.1 ≠ 1 := by
          intro h1; apply hne18; ext; exact h1; omega
        have hne2 : b.1 ≠ 2 := by
          intro h2; apply hne27; ext; exact h2; omega
        have hne3 : b.1 ≠ 3 := by
          intro h3; apply hne36; ext; exact h3; omega
        have hne4 : b.1 ≠ 4 := by
          intro h4; apply hne45; ext; exact h4; omega
        have hne5 : b.1 ≠ 5 := by
          intro h5; apply hne54; ext; exact h5; omega
        have hne6 : b.1 ≠ 6 := by
          intro h6; apply hne63; ext; exact h6; omega
        have hj : 10 ≤ b.2 := by omega
        simp [hgd_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4),
            (6, 3)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 9 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 8 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 5 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 6 * g.derivative.coeff 3 := by
      rw [Finset.sum_insert (by simp [hne09_18, hne09_27, hne09_36, hne09_45,
            hne09_54, hne09_63]),
        Finset.sum_insert (by simp [hne18_27, hne18_36, hne18_45, hne18_54,
            hne18_63]),
        Finset.sum_insert (by simp [hne27_36, hne27_45, hne27_54, hne27_63]),
        Finset.sum_insert (by simp [hne36_45, hne36_54, hne36_63]),
        Finset.sum_insert (by simp [hne45_54, hne45_63]),
        Finset.sum_insert (by simp [hne54_63]), Finset.sum_singleton]
      ring
    have hder9 : g.derivative.coeff 9 = (10 : F) := by
      rw [Polynomial.coeff_derivative, hg10]
      norm_num
    have hder8 : g.derivative.coeff 8 = (9 : F) * g.coeff 9 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : g.derivative.coeff 7 = (8 : F) * g.coeff 8 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder6 : g.derivative.coeff 6 = (7 : F) * g.coeff 7 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, hder9, hder8, hder7,
      hder6, hder5, hder4, hder3]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 9 =
        (2 : F) * f.coeff 2 * d (g.coeff 8) +
          (3 : F) * f.coeff 3 * d (g.coeff 7) +
          (4 : F) * f.coeff 4 * d (g.coeff 6) +
          (5 : F) * f.coeff 5 * d (g.coeff 5) +
          (6 : F) * f.coeff 6 * d (g.coeff 4) +
          (8 : F) * d (g.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne18_27 : ((1, 8) : ℕ × ℕ) ≠ (2, 7) := by decide
    have hne18_36 : ((1, 8) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne18_45 : ((1, 8) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne18_54 : ((1, 8) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne18_72 : ((1, 8) : ℕ × ℕ) ≠ (7, 2) := by decide
    have hne27_36 : ((2, 7) : ℕ × ℕ) ≠ (3, 6) := by decide
    have hne27_45 : ((2, 7) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne27_54 : ((2, 7) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne27_72 : ((2, 7) : ℕ × ℕ) ≠ (7, 2) := by decide
    have hne36_45 : ((3, 6) : ℕ × ℕ) ≠ (4, 5) := by decide
    have hne36_54 : ((3, 6) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne36_72 : ((3, 6) : ℕ × ℕ) ≠ (7, 2) := by decide
    have hne45_54 : ((4, 5) : ℕ × ℕ) ≠ (5, 4) := by decide
    have hne45_72 : ((4, 5) : ℕ × ℕ) ≠ (7, 2) := by decide
    have hne54_72 : ((5, 4) : ℕ × ℕ) ≠ (7, 2) := by decide
    have hsubset :
        ({(1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (7, 2)} :
            Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (9 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb | hb
      · subst b; exact hmem18
      · subst b; exact hmem27
      · subst b; exact hmem36
      · subst b; exact hmem45
      · subst b; exact hmem54
      · subst b; exact hmem72
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (9 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (7, 2)} :
              Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 9 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne18 : b ≠ (1, 8) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne27 : b ≠ (2, 7) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne36 : b ≠ (3, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne45 : b ≠ (4, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne54 : b ≠ (5, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne72 : b ≠ (7, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 8 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h6 : b.1 = 6
        · have hf6 : f.derivative.coeff b.1 = 0 := by
            rw [h6, Polynomial.coeff_derivative, hf7]
            simp
          simp [hf6]
        · by_cases h0 : b.1 = 0
          · have hj : 9 ≤ b.2 := by omega
            simp [hgd'_high b.2 hj]
          · have hne1 : b.1 ≠ 1 := by
              intro h1; apply hne18; ext; exact h1; omega
            have hne2 : b.1 ≠ 2 := by
              intro h2; apply hne27; ext; exact h2; omega
            have hne3 : b.1 ≠ 3 := by
              intro h3; apply hne36; ext; exact h3; omega
            have hne4 : b.1 ≠ 4 := by
              intro h4; apply hne45; ext; exact h4; omega
            have hne5 : b.1 ≠ 5 := by
              intro h5; apply hne54; ext; exact h5; omega
            have hne7 : b.1 ≠ 7 := by
              intro h7; apply hne72; ext; exact h7; omega
            have hj : 9 ≤ b.2 := by omega
            simp [hgd'_high b.2 hj]
    have hpair :
        (∑ p ∈ ({(1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (7, 2)} :
            Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 1 * (coefficientDeriv d g).coeff 8 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 4 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 7 * (coefficientDeriv d g).coeff 2 := by
      rw [Finset.sum_insert (by simp [hne18_27, hne18_36, hne18_45, hne18_54,
            hne18_72]),
        Finset.sum_insert (by simp [hne27_36, hne27_45, hne27_54, hne27_72]),
        Finset.sum_insert (by simp [hne36_45, hne36_54, hne36_72]),
        Finset.sum_insert (by simp [hne45_54, hne45_72]),
        Finset.sum_insert (by simp [hne54_72]), Finset.sum_singleton]
      ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : f.derivative.coeff 4 = (5 : F) * f.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) * f.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder7 : f.derivative.coeff 7 = (8 : F) := by
      rw [Polynomial.coeff_derivative, hf8]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder1, hder2, hder3, hder4, hder5, hder7]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 8000000 in
theorem etaResidual810_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hrow : (10 : F) * d G0 + (9 : F) * L * d F0 +
        (8 : F) * P * d E0 + (7 : F) * Q * d D0 +
        (6 : F) * R * d C0 + (5 : F) * S0 * d B +
        (4 : F) * T0 * d A -
        (2 : F) * E0 * d P - (3 : F) * D0 * d Q -
        (4 : F) * C0 * d R - (5 : F) * B * d S0 -
        (6 : F) * A * d T0 - (8 : F) * d V0 = 0) :
    d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h1024 : d (1024 : F) = 0 := d.map_natCast 1024
  have h2048 : d (2048 : F) = 0 := d.map_natCast 2048
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h58 : d (5 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h5]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h5]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h5]
  have h15128 : d (15 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h15]
  have h352048 : d (35 / 2048 : F) = 0 := by
    simp [Derivation.leibniz_div, h2048, h35]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h9]
  have h631024 : d (63 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024, h63]
  have h764 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h7]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h3]
  have h5128 : d (5 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h5]
  have h9128 : d (9 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h9]
  have hPderiv : d P = (5 / 4 : F) * d A := by
    have halpha' : d P - (5 / 4 : F) * d A = 0 := by
      simpa [alphaResidual810, map_sub, Derivation.leibniz, h54, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 4 : F) * d B + (9 / 8 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
      simpa [betaResidual810, map_sub, Derivation.leibniz, h54, h98, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hgamma_id :
      d (gammaResidual810 L A B C0 P R) =
        d R - ((5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
          (9 / 8 : F) * L * d B + alphaResidual810 A P * d A) := by
    simp only [gammaResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h532, hL, halpha, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hRderiv' :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + alphaResidual810 A P * d A := by
    linear_combination hgamma_id.symm + hgamma
  have hRderiv :
      d R = (5 / 4 : F) * d C0 + (5 / 16 : F) * A * d A +
        (9 / 8 : F) * L * d B + (P - (5 / 4 : F) * A) * d A := by
    rw [hRderiv']
    simp only [alphaResidual810]
  have hdelta_id :
      d (deltaResidual810 L A B C0 D0 P Q S0) =
        d S0 - ((5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
          alphaResidual810 A P * d B +
          (7 / 8 : F) * betaResidual810 L A B Q * d A +
          (5 / 16 : F) * (A * d B + B * d A) +
          (9 / 64 : F) * L * A * d A) := by
    unfold deltaResidual810
    simp [map_sub, map_add, Derivation.leibniz, h54, h98, h78, h516, h964,
      h9128, hL, halpha, hbeta, zero_mul, add_zero, mul_zero, pow_two, hsq]
    ring
  have hSderiv' :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        alphaResidual810 A P * d B +
        (7 / 8 : F) * betaResidual810 L A B Q * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    linear_combination hdelta_id.symm + hdelta
  have hSderiv :
      d S0 = (5 / 4 : F) * d D0 + (9 / 8 : F) * L * d C0 +
        (P - (5 / 4 : F) * A) * d B +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d A +
        (5 / 16 : F) * (A * d B + B * d A) +
        (9 / 64 : F) * L * A * d A := by
    rw [hSderiv']
    simp [alphaResidual810, betaResidual810]
  have hepsilon_id :
      d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) =
        d T0 - ((5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
          (5 / 16 : F) * (A * d C0 + C0 * d A) -
          (15 / 128 : F) * A ^ 2 * d A +
          L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
          alphaResidual810 A P * d C0 +
          (7 / 8 : F) * betaResidual810 L A B Q * d B +
          (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A) := by
    simp only [epsilonResidual810, map_sub, map_add, Derivation.leibniz, h54,
      h98, h78, h34, h532, h516, h5128, h15128, h964, hL, halpha, hbeta,
      hgamma, zero_mul, add_zero, mul_zero, pow_two, hsq, hsqB, hcub]
    ring
  have hTderiv' :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        alphaResidual810 A P * d C0 +
        (7 / 8 : F) * betaResidual810 L A B Q * d B +
        (3 / 4 : F) * gammaResidual810 L A B C0 P R * d A := by
    linear_combination hepsilon_id.symm + hepsilon
  have hTderiv :
      d T0 = (5 / 4 : F) * d E0 + (5 / 16 : F) * B * d B +
        (5 / 16 : F) * (A * d C0 + C0 * d A) -
        (15 / 128 : F) * A ^ 2 * d A +
        L * ((9 / 8 : F) * d D0 + (9 / 64 : F) * (A * d B + B * d A)) +
        (P - (5 / 4 : F) * A) * d C0 +
        (7 / 8 : F) * (Q - (5 / 4 : F) * B - (9 / 8 : F) * L * A) * d B +
        (3 / 4 : F) * (R - ((5 / 4 : F) * C0 + (5 / 32 : F) * A ^ 2 +
          (9 / 8 : F) * L * B + (P - (5 / 4 : F) * A) * A)) * d A := by
    rw [hTderiv']
    simp [gammaResidual810, alphaResidual810, betaResidual810]
  have hVderiv :
      d V0 = (5 / 4 : F) * d G0 + (9 / 8 : F) * L * d F0 +
        P * d E0 + (7 / 8 : F) * Q * d D0 + (3 / 4 : F) * R * d C0 +
        (5 / 8 : F) * S0 * d B + (1 / 2 : F) * T0 * d A -
        (1 / 4 : F) * E0 * d P - (3 / 8 : F) * D0 * d Q -
        (1 / 2 : F) * C0 * d R - (5 / 8 : F) * B * d S0 -
        (3 / 4 : F) * A * d T0 := by
    linear_combination (-1 / 8 : F) * hrow
  simp only [etaResidual810, alphaResidual810, betaResidual810,
    gammaResidual810, deltaResidual810, epsilonResidual810, map_sub, map_add,
    Derivation.leibniz, h12, h14, h38, h54, h98, h78, h34, h58, h516, h532, h15128,
    h352048, h964, h631024, h764, h332, h5128, h9128, hL, zero_mul, add_zero,
    mul_zero, pow_two, hsq, hsqB, hsqC, hcub, hquar]
  rw [hVderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv]
  ring

end DepressedRow810Eighth

/-! ## Sixth-jet parenthetical of the sixth defect -/

section EighthFaceScalars810

variable {F : Type*} [Field F] [CharZero F]

/-- Parenthetical of the sixth-face jet in the cleared sixth defect. -/
def sixthJetParen810_sixth
    (h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4 : F[X]) (lambda : F) : F[X] :=
  -(98304 : F[X]) * b6 * v0 + (98304 : F[X]) * s0 * v0 ^ 2 -
    (102400 : F[X]) * v0 ^ 3 +
    ((73728 : F[X]) * b6 * t0 ^ 2 -
        (245760 : F[X]) * s0 * t0 ^ 2 * v0 +
      (196608 : F[X]) * s0 * t0 * u0 +
        (192000 : F[X]) * t0 ^ 2 * v0 ^ 2 -
      (337920 : F[X]) * t0 * u0 * v0 +
        (172032 : F[X]) * t0 * v0 * w0 +
      (122880 : F[X]) * u0 ^ 2 - (114688 : F[X]) * u0 * w0) * h +
    (-(131072 : F[X]) * a4 * s0 + (245760 : F[X]) * a4 * v0 +
        (69120 : F[X]) * Polynomial.C lambda * t0 * v0 ^ 2 -
      (55296 : F[X]) * Polynomial.C lambda * u0 * v0 +
        (71680 : F[X]) * s0 * t0 ^ 4 +
      (12800 : F[X]) * t0 ^ 3 * u0 -
        (71680 : F[X]) * t0 ^ 3 * w0) * h ^ 2 +
    (-(30720 : F[X]) * a4 * t0 ^ 2 - (81920 : F[X]) * b5 * t0 -
        (80640 : F[X]) * Polynomial.C lambda * t0 ^ 3 * v0 +
      (69120 : F[X]) * Polynomial.C lambda * t0 ^ 2 * u0 -
        (16800 : F[X]) * t0 ^ 6) * h ^ 3 +
    (-(55296 : F[X]) * a4 * Polynomial.C lambda * t0 +
        (18144 : F[X]) * Polynomial.C lambda * t0 ^ 5) * h ^ 4 +
    ((61440 : F[X]) * a3 * t0 + (131072 : F[X]) * b4) * h ^ 5 +
    ((36864 : F[X]) * a3 * Polynomial.C lambda) * h ^ 6 +
    (-(163840 : F[X]) * a2) * h ^ 7

/-- Cofactor of `h` in the sixth-jet sixth defect after the left
seventh-packet vanishing `v₀ = h v₁`, `s₀ = h s₁`, `b₆ = h b₆₁`. -/
def sixthJetParen810_sixth_leftCofactor
    (h t0 v1 s1 w0 u0 a4 a3 a2 b61 b5 b4 : F[X]) (lambda : F) : F[X] :=
  (122880 : F[X]) * u0 ^ 2 - (114688 : F[X]) * u0 * w0 +
    ((73728 : F[X]) * b61 * t0 ^ 2 - (98304 : F[X]) * b61 * v1 +
        (196608 : F[X]) * s1 * t0 * u0 +
      (12800 : F[X]) * t0 ^ 3 * u0 - (71680 : F[X]) * t0 ^ 3 * w0 -
        (337920 : F[X]) * t0 * u0 * v1 +
      (172032 : F[X]) * t0 * v1 * w0) * h +
    (-(131072 : F[X]) * a4 * s1 - (30720 : F[X]) * a4 * t0 ^ 2 +
        (245760 : F[X]) * a4 * v1 - (81920 : F[X]) * b5 * t0 +
      (69120 : F[X]) * Polynomial.C lambda * t0 ^ 2 * u0 -
        (55296 : F[X]) * Polynomial.C lambda * u0 * v1 +
      (71680 : F[X]) * s1 * t0 ^ 4 -
        (245760 : F[X]) * s1 * t0 ^ 2 * v1 +
      (98304 : F[X]) * s1 * v1 ^ 2 - (16800 : F[X]) * t0 ^ 6 +
        (192000 : F[X]) * t0 ^ 2 * v1 ^ 2 -
      (102400 : F[X]) * v1 ^ 3) * h ^ 2 +
    (-(55296 : F[X]) * a4 * Polynomial.C lambda * t0 +
        (18144 : F[X]) * Polynomial.C lambda * t0 ^ 5 -
      (80640 : F[X]) * Polynomial.C lambda * t0 ^ 3 * v1 +
        (69120 : F[X]) * Polynomial.C lambda * t0 * v1 ^ 2) * h ^ 3 +
    ((61440 : F[X]) * a3 * t0 + (131072 : F[X]) * b4) * h ^ 4 +
    ((36864 : F[X]) * a3 * Polynomial.C lambda) * h ^ 5 +
    (-(163840 : F[X]) * a2) * h ^ 6

set_option maxHeartbeats 8000000 in
theorem localClearedSixthDefect810_of_sixthJet
    (h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4 : F[X]) (lambda : F) :
    localClearedSixthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h * u0) a4 a3
        a2 (h ^ 5 * s0) (h ^ 3 * w0) b6 b5 b4 lambda =
      h ^ 33 * sixthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4
        lambda := by
  simp only [localClearedSixthDefect810, sixthJetParen810_sixth]
  ring

set_option maxHeartbeats 4000000 in
theorem sixthJetParen810_sixth_left_mul_h
    (h t0 v1 s1 w0 u0 a4 a3 a2 b61 b5 b4 : F[X]) (lambda : F) :
    sixthJetParen810_sixth h t0 (h * v1) (h * s1) w0 u0 a4 a3 a2
        (h * b61) b5 b4 lambda =
      h * sixthJetParen810_sixth_leftCofactor h t0 v1 s1 w0 u0 a4 a3 a2
        b61 b5 b4 lambda := by
  simp only [sixthJetParen810_sixth, sixthJetParen810_sixth_leftCofactor]
  ring

theorem sixthJetParen810_sixth_eq_of_power
    (h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4 : F[X]) (lambda zeta : F)
    (hh : h ≠ 0)
    (hW : localClearedSixthDefect810 h (h ^ 6 * t0) (h ^ 3 * v0) (h * u0)
        a4 a3 a2 (h ^ 5 * s0) (h ^ 3 * w0) b6 b5 b4 lambda =
      Polynomial.C zeta * h ^ 42) :
    sixthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4 lambda =
      Polynomial.C zeta * h ^ 9 := by
  have hfactor :=
    localClearedSixthDefect810_of_sixthJet h t0 v0 s0 w0 u0 a4 a3 a2 b6
      b5 b4 lambda
  have hscale : Polynomial.C zeta * h ^ 42 =
      h ^ 33 * (Polynomial.C zeta * h ^ 9) := by ring
  apply mul_left_cancel₀ (pow_ne_zero 33 hh)
  rw [← hfactor, hW, hscale]

theorem eval_sixthJetParen810_sixth
    (h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (sixthJetParen810_sixth h t0 v0 s0 w0 u0 a4 a3 a2 b6 b5 b4
          lambda) =
      -(98304 : F) * Polynomial.eval root b6 * Polynomial.eval root v0 +
        (98304 : F) * Polynomial.eval root s0 *
          (Polynomial.eval root v0) ^ 2 -
        (102400 : F) * (Polynomial.eval root v0) ^ 3 := by
  simp [sixthJetParen810_sixth, hroot]

theorem eval_sixthJetParen810_sixth_leftCofactor
    (h t0 v1 s1 w0 u0 a4 a3 a2 b61 b5 b4 : F[X]) (lambda : F)
    (root : F) (hroot : Polynomial.eval root h = 0) :
    Polynomial.eval root
        (sixthJetParen810_sixth_leftCofactor h t0 v1 s1 w0 u0 a4 a3 a2
          b61 b5 b4 lambda) =
      (122880 : F) * (Polynomial.eval root u0) ^ 2 -
        (114688 : F) * Polynomial.eval root u0 *
          Polynomial.eval root w0 := by
  simp [sixthJetParen810_sixth_leftCofactor, hroot]

/-- On the `t₀ = 0` seventh-packet component, the sixth defect forces
`v₀ = 0`, hence also `s₀ = b₆ = 0`. -/
theorem eighthFace_right_v0_810 (v0 s0 b6 : F)
    (hs : (4 : F) * s0 = (5 : F) * v0)
    (hb : (32 : F) * b6 = (5 : F) * v0 ^ 2)
    (hK33 : -(98304 : F) * b6 * v0 + (98304 : F) * s0 * v0 ^ 2 -
        (102400 : F) * v0 ^ 3 = 0) :
    v0 = 0 ∧ s0 = 0 ∧ b6 = 0 := by
  have hsrel : (4 : F) * s0 - (5 : F) * v0 = 0 := by
    linear_combination hs
  have hbrel : (32 : F) * b6 - (5 : F) * v0 ^ 2 = 0 := by
    linear_combination hb
  have h5120 : (5120 : F) ≠ 0 := by norm_num
  have hcomb : (5120 : F) * v0 ^ 3 = 0 := by
    linear_combination hK33 + (3072 : F) * v0 * hbrel -
      (24576 : F) * v0 ^ 2 * hsrel
  have hv0 : v0 = 0 := by
    have : v0 ^ 3 = 0 :=
      (mul_eq_zero.mp hcomb).resolve_left h5120
    exact eq_zero_of_pow_eq_zero this
  have hs0 : s0 = 0 := by
    have h4 : (4 : F) ≠ 0 := by norm_num
    have : (4 : F) * s0 = 0 := by
      simpa [hv0] using hs
    exact (mul_eq_zero.mp this).resolve_left h4
  have hb0 : b6 = 0 := by
    have h32 : (32 : F) ≠ 0 := by norm_num
    have : (32 : F) * b6 = 0 := by
      simpa [hv0] using hb
    exact (mul_eq_zero.mp this).resolve_left h32
  exact ⟨hv0, hs0, hb0⟩

/-- On the `v₀ = 0` seventh-packet component, the next sixth-defect
coefficient forces `u₀ = 0`, hence also `w₀ = 0`. -/
theorem eighthFace_left_u0_810 (u0 w0 : F)
    (hw : (4 : F) * w0 = (5 : F) * u0)
    (hK34 : (122880 : F) * u0 ^ 2 - (114688 : F) * u0 * w0 = 0) :
    u0 = 0 ∧ w0 = 0 := by
  have hwrel : (4 : F) * w0 - (5 : F) * u0 = 0 := by
    linear_combination hw
  have h20480 : (20480 : F) ≠ 0 := by norm_num
  have hcomb : -(20480 : F) * u0 ^ 2 = 0 := by
    linear_combination hK34 + (28672 : F) * u0 * hwrel
  have hu0 : u0 = 0 := by
    have : (20480 : F) * u0 ^ 2 = 0 := by
      linear_combination -hcomb
    have hsq : u0 ^ 2 = 0 :=
      (mul_eq_zero.mp this).resolve_left h20480
    exact eq_zero_of_pow_eq_zero hsq
  have hw0 : w0 = 0 := by
    have h4 : (4 : F) ≠ 0 := by norm_num
    have : (4 : F) * w0 = 0 := by
      simpa [hu0] using hw
    exact (mul_eq_zero.mp this).resolve_left h4
  exact ⟨hu0, hw0⟩

end EighthFaceScalars810

/-! ## Source-facing eighth-face packet -/

section NonzeroEighthFace810

variable {k : Type*} [Field k] [CharZero k]

/-- Finite local eighth-face packet: the seventh-face split together with
the sixth-defect refinements of both components. -/
theorem nonzeroFace810_linearRoot_eighthInitialPacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda a : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hh0degree : h0.natDegree = 1) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hroot : h0.eval a = 0) :
    ∃ t0 v0 u0 s0 w0 : k[X],
      p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (4 : k) * w0.eval a = (5 : k) * u0.eval a ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : k) * s0.eval a = (5 : k) * v0.eval a ∧
            (32 : k) * (q.coeff 6).eval a = (5 : k) * (v0.eval a) ^ 2 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧ h0 ∣ q.coeff 6)) := by
  obtain ⟨zeta, hWrel⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H h0 j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  obtain ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9d, hsplit⟩ :=
    nonzeroFace810_linearRoot_seventhInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8 hq10 hN hD hroot
  have hWsubst :
      localClearedSixthDefect810 h0 (h0 ^ 6 * t0) (h0 ^ 3 * v0)
          (h0 * u0) (p.coeff 4) (p.coeff 3) (p.coeff 2) (h0 ^ 5 * s0)
          (h0 ^ 3 * w0) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        localClearedSixthDefect810 h0 (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda := by
    simp only [ht0, hv0, hu0, hs0, hw0]
  have hWparen :
      sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * h0 ^ 9 :=
    sixthJetParen810_sixth_eq_of_power h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (p.coeff 2) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda
      zeta hh0 (hWsubst.trans hWrel)
  have hWroot :=
    eval_sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
      (p.coeff 3) (p.coeff 2) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda
      a hroot
  have hK33 :
      -(98304 : k) * (q.coeff 6).eval a * v0.eval a +
          (98304 : k) * s0.eval a * (v0.eval a) ^ 2 -
          (102400 : k) * (v0.eval a) ^ 3 = 0 := by
    have hzero :
        Polynomial.eval a
            (sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) lambda) = 0 := by
      rw [hWparen]
      simp [hroot]
    rw [← hWroot]
    exact hzero
  rcases hsplit with hleft | hright
  · obtain ⟨hv0z, hs0z, hb6z, hwrel, hp6_4, hq8_6, hq6div⟩ := hleft
    obtain ⟨v1, hv1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 v0 a hh0degree hroot hv0z
    obtain ⟨s1, hs1⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 s0 a hh0degree hroot hs0z
    obtain ⟨b61, hb61⟩ :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 6) a hh0degree
        hroot hb6z
    have hleftmul :=
      sixthJetParen810_sixth_left_mul_h h0 t0 v1 s1 w0 u0 (p.coeff 4)
        (p.coeff 3) (p.coeff 2) b61 (q.coeff 5) (q.coeff 4) lambda
    have hWleft :
        sixthJetParen810_sixth h0 t0 v0 s0 w0 u0 (p.coeff 4) (p.coeff 3)
            (p.coeff 2) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
          h0 * sixthJetParen810_sixth_leftCofactor h0 t0 v1 s1 w0 u0
            (p.coeff 4) (p.coeff 3) (p.coeff 2) b61 (q.coeff 5)
            (q.coeff 4) lambda := by
      simpa [hv1, hs1, hb61] using hleftmul
    have hcof :
        sixthJetParen810_sixth_leftCofactor h0 t0 v1 s1 w0 u0
            (p.coeff 4) (p.coeff 3) (p.coeff 2) b61 (q.coeff 5)
            (q.coeff 4) lambda =
          Polynomial.C zeta * h0 ^ 8 := by
      apply mul_left_cancel₀ hh0
      have hscale : Polynomial.C zeta * h0 ^ 9 =
          h0 * (Polynomial.C zeta * h0 ^ 8) := by ring
      rw [← hWleft, hWparen, hscale]
    have hK34 :
        (122880 : k) * (u0.eval a) ^ 2 -
            (114688 : k) * u0.eval a * w0.eval a = 0 := by
      have hleft :=
        eval_sixthJetParen810_sixth_leftCofactor h0 t0 v1 s1 w0 u0
          (p.coeff 4) (p.coeff 3) (p.coeff 2) b61 (q.coeff 5)
          (q.coeff 4) lambda a hroot
      have hzero :
          Polynomial.eval a
              (sixthJetParen810_sixth_leftCofactor h0 t0 v1 s1 w0 u0
                (p.coeff 4) (p.coeff 3) (p.coeff 2) b61 (q.coeff 5)
                (q.coeff 4) lambda) = 0 := by
        rw [hcof]
        simp [hroot]
      rw [← hleft]
      exact hzero
    obtain ⟨hu0z, hw0z⟩ := eighthFace_left_u0_810 (u0.eval a) (w0.eval a)
      hwrel hK34
    have hp5_2 : h0 ^ 2 ∣ p.coeff 5 := by
      have htmp :=
        pow_dvd_mul_of_eval_eq_zero_810 h0 u0 1 a hh0degree hroot hu0z
      simpa [hu0, pow_one] using htmp
    have hq7_4 : h0 ^ 4 ∣ q.coeff 7 := by
      rw [hw0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 w0 3 a hh0degree hroot hw0z
    exact ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9d,
      Or.inl ⟨hv0z, hs0z, hb6z, hu0z, hw0z, hwrel, hp6_4, hq8_6, hq6div,
        hp5_2, hq7_4⟩⟩
  · obtain ⟨ht0z, hu0z, hw0z, hsrel, hbrel, hp7_7, hp5_2, hq7_4⟩ := hright
    obtain ⟨hv0z, hs0z, hb6z⟩ :=
      eighthFace_right_v0_810 (v0.eval a) (s0.eval a) ((q.coeff 6).eval a)
        hsrel hbrel hK33
    have hp6_4 : h0 ^ 4 ∣ p.coeff 6 := by
      rw [hv0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 v0 3 a hh0degree hroot hv0z
    have hq8_6 : h0 ^ 6 ∣ q.coeff 8 := by
      rw [hs0]
      exact pow_dvd_mul_of_eval_eq_zero_810 h0 s0 5 a hh0degree hroot hs0z
    have hq6div : h0 ∣ q.coeff 6 :=
      linearPolynomial_dvd_of_eval_eq_zero_810 h0 (q.coeff 6) a hh0degree
        hroot hb6z
    exact ⟨t0, v0, u0, s0, w0, ht0, hv0, hu0, hs0, hw0, hq9d,
      Or.inr ⟨ht0z, hu0z, hw0z, hv0z, hs0z, hb6z, hsrel, hbrel, hp7_7,
        hp5_2, hq7_4, hp6_4, hq8_6, hq6div⟩⟩

/-- Source-facing eighth-face packet of a normalized scale-two `(8,10)`
nonzero face: the seventh-face split together with the sixth-defect
refinements of both components. -/
theorem normalized810ScaleTwo_nonzeroFace_eighthInitialPacket
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (h0 : K[X]) (lambda a : K) (t0 v0 u0 s0 w0 : K[X]),
      h0 ≠ 0 ∧ lambda ≠ 0 ∧ h0.natDegree = 1 ∧ H = h0 ^ 2 ∧
        h0.eval a = 0 ∧
        p.coeff 7 = h0 ^ 6 * t0 ∧ p.coeff 6 = h0 ^ 3 * v0 ∧
        p.coeff 5 = h0 * u0 ∧ q.coeff 8 = h0 ^ 5 * s0 ∧
        q.coeff 7 = h0 ^ 3 * w0 ∧ h0 ^ 8 ∣ q.coeff 9 ∧
        (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
          Polynomial.C lambda * h0 ^ 9 ∧
        ((v0.eval a = 0 ∧ s0.eval a = 0 ∧ (q.coeff 6).eval a = 0 ∧
            u0.eval a = 0 ∧ w0.eval a = 0 ∧
            (4 : K) * w0.eval a = (5 : K) * u0.eval a ∧
            h0 ^ 4 ∣ p.coeff 6 ∧ h0 ^ 6 ∣ q.coeff 8 ∧
            h0 ∣ q.coeff 6 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7) ∨
          (t0.eval a = 0 ∧ u0.eval a = 0 ∧ w0.eval a = 0 ∧
            v0.eval a = 0 ∧ s0.eval a = 0 ∧
            (q.coeff 6).eval a = 0 ∧
            (4 : K) * s0.eval a = (5 : K) * v0.eval a ∧
            (32 : K) * (q.coeff 6).eval a = (5 : K) * (v0.eval a) ^ 2 ∧
            h0 ^ 7 ∣ p.coeff 7 ∧ h0 ^ 2 ∣ p.coeff 5 ∧
            h0 ^ 4 ∣ q.coeff 7 ∧ h0 ^ 4 ∣ p.coeff 6 ∧
            h0 ^ 6 ∣ q.coeff 8 ∧ h0 ∣ q.coeff 6)) := by
  dsimp only at hnonzero ⊢
  obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
    normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hnonzero
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨t0', v0', u0', s0', w0', ht0', hv0', hu0', hs0', hw0', hq9',
    hsplit'⟩ :=
    nonzeroFace810_linearRoot_eighthInitialPacket p q H h0 j lambda a
      hp hq hh0 hh0degree hH hp8' hq10' hN' hD hroot
  exact ⟨h0, lambda, a, t0', v0', u0', s0', w0', hh0, hlambda, hh0degree,
    hH, hroot, ht0', hv0', hu0', hs0', hw0', hq9', hN', hsplit'⟩

end NonzeroEighthFace810

#print axioms eighthCoefficientJacobianRow_810
#print axioms differentialJacobian_coeff_9_monicOcticDecic
#print axioms etaResidual810_deriv_zero
#print axioms eighthFace_right_v0_810
#print axioms eighthFace_left_u0_810
#print axioms nonzeroFace810_linearRoot_eighthInitialPacket
#print axioms normalized810ScaleTwo_nonzeroFace_eighthInitialPacket

end Max11DegreeRoutes
