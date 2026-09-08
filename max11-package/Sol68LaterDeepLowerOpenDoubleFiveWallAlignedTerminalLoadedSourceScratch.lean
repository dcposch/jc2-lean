import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSourceScratch

/-! # The loaded terminal of the aligned double-five descent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedTerminalLoadedSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 12000000 in
theorem secondaryResidualRowOnePolynomial68_coeff_terminal_aligned_fiveWall
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - 2 * g)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 4 * g - 1) =
      (-4 / 27 : k) *
        (2 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * d.coeff 0 *
            ((5 * n - g : ℕ) : k) -
          6 * A.coeff (2 * n) * c.coeff (4 * n - 2 * g) *
            e.coeff (6 * n - 2 * g) * ((5 * n - g : ℕ) : k) -
          4 * (n : k) * A.coeff (2 * n) *
            B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - 2 * g) -
          3 * B.coeff (3 * n - g) ^ 2 *
            e.coeff (6 * n - 2 * g) * ((6 * n - 2 * g : ℕ) : k) -
          18 * e.coeff (6 * n - 2 * g) ^ 2 *
            ((6 * n - 2 * g : ℕ) : k)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have hp := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using hp
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hp := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hp
  have hdd : derivative d = 0 := derivative_eq_zero.mpr (Nat.le_zero.mp hd)
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) 0 (3 * n - g) (by omega) hA2deg hd hB
  have hi2 : 4 * n + 0 + (3 * n - g) - 1 =
      12 * n - 4 * g - 1 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff (12 * n - 4 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * d.coeff 0 *
        ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) 0 (2 * n) (by omega) hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + 0 + 2 * n - 1 =
      12 * n - 4 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff (12 * n - 4 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff 0 * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - 2 * g) (6 * n - 2 * g) (by omega) hA hc he
  have hi4 : 2 * n + (4 * n - 2 * g) + (6 * n - 2 * g) - 1 =
      12 * n - 4 * g - 1 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - 2 * g) (by omega) hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - 2 * g) - 1 =
      12 * n - 4 * g - 1 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff (12 * n - 4 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - 2 * g) *
        e.coeff (6 * n - 2 * g) * ((4 * n - 2 * g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - 2 * g) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - 2 * g) + 2 * n - 1 =
      12 * n - 4 * g - 1 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff (12 * n - 4 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_derivative_at_bounds68 (B ^ 2) e
    (6 * n - 2 * g) (6 * n - 2 * g) (by omega) hB2deg he
  have hi7 : (6 * n - 2 * g) + (6 * n - 2 * g) - 1 =
      12 * n - 4 * g - 1 := by omega
  rw [hi7, hB2] at h7
  have h8 := coeff_mul_derivative_at_bounds68 e e
    (6 * n - 2 * g) (6 * n - 2 * g) (by omega) he he
  rw [hi7] at h8
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 4 * g - 1 := by compute_degree; omega
  have hlowB : (B * derivative c * d).natDegree <
      12 * n - 4 * g - 1 := by compute_degree; omega
  have hlowC : (derivative B * c * d).natDegree <
      12 * n - 4 * g - 1 := by compute_degree; omega
  have hlowD : (c ^ 2 * derivative c).natDegree <
      12 * n - 4 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowOnePolynomial68, hdd,
    mul_zero, coeff_smul, coeff_add, coeff_sub, h2', h3', h4, h5', h6',
    h7, h8, coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD, zero_smul, coeff_zero,
    smul_eq_mul]
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by push_cast; rfl
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - 2 * g : ℕ) : k)) =
      4 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 4 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 5 * n)]
    push_cast
    rfl
  rw [hcast2, hcast3, hcast4, hcast6, hcast5]
  have hw : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
  linear_combination
    (-8 / 9 : k) * A.coeff (2 * n) * c.coeff (4 * n - 2 * g) *
      e.coeff (6 * n - 2 * g) * hw

set_option maxHeartbeats 12000000 in
theorem cubicLoadRowOnePolynomial68_coeff_terminal_aligned_fiveWall
    (alpha gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - 2 * g)
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (12 * n - 4 * g - 1) =
      (-1 / 6 : k) * delta * A.coeff (2 * n) ^ 2 *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest 0 alpha 0 gamma delta
      epsilon zeta eta A B c ((1 / 3 : k) • (A * B) + d) e rfl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  let Dtr := (1 / 3 : k) • (A * B) + d
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c Dtr e
  let Vtail := (2 / 3 * gamma : k) • c +
    (1 / 2 * delta : k) • B + C eta
  let C0c := (1 / 3 : k) • A ^ 2
  let Er := (1 / 3 : k) • (A * c) + e
  have hgt : n < g := by omega
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB (hc.trans (by omega))
  have hDtr : Dtr.natDegree ≤ 5 * n - g := by
    simp only [Dtr]
    compute_degree
    omega
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_laterDeepLower_le_two
      alpha 0 gamma delta epsilon eta A B c Dtr e n g hn
      (by omega) (by omega) hA hB (hc.trans (by omega)) hDtr
      (he.trans (by omega))
  have hVtail : Vtail.natDegree ≤ 3 * n - g := by
    simp only [Vtail]
    compute_degree
    omega
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - 2 * g := by
    simp only [Er]
    compute_degree
    omega
  have hdecomp :
      cubicLoadRowOneDeepGapRestPolynomial68 alpha 0 gamma delta epsilon
          zeta eta A B c Dtr e =
        Ur * derivative Dtr +
          (2 : k) • ((alpha • c) * derivative Er) +
          (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
          (2 : k) • ((C epsilon : k[X]) * derivative Er) -
          (2 : k) • (C0c * derivative Vtail) -
          (2 : k) • (c * derivative Vr) -
          Dtr * derivative Ur := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowOneDeepGapRestPolynomial68, Ur, Vr, Vtail,
      C0c, Er, cubicLoadVAlphaLowPolynomial68, zero_mul, zero_smul,
      zero_add, add_zero, sub_zero, derivative_add, derivative_smul,
      derivative_pow, derivative_mul, derivative_C,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_zero, RatFunc.algebraMap_C]
    simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  rw [hdecomp]
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  have hABi : 2 * n + (3 * n - g) = 5 * n - g := by omega
  rw [hABi] at hAB
  have hDtop : Dtr.coeff (5 * n - g) =
      (1 / 3 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) := by
    have hdtop : d.coeff (5 * n - g) = 0 :=
      coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
    simp only [Dtr, coeff_add, coeff_smul, hAB, hdtop, add_zero, smul_eq_mul]
    ring
  have hUtop : Ur.coeff (2 * n) =
      (1 / 2 : k) * delta * A.coeff (2 * n) := by
    have hBc : (((2 / 3 * gamma : k) • B).natDegree < 2 * n) :=
      (natDegree_smul_le _ B).trans_lt (hB.trans_lt (by omega))
    have hcc : (((5 / 6 * (0 : k) : k) • c).natDegree < 2 * n) := by
      simp only [mul_zero, zero_smul, natDegree_zero]
      omega
    have hc' : (((5 / 24 * (0 : k) : k) • A ^ 2).natDegree < 2 * n) := by
      simp only [mul_zero, zero_smul, natDegree_zero]
      omega
    have hC : (C zeta : k[X]).natDegree < 2 * n := by
      rw [natDegree_C]
      omega
    simp only [Ur, cubicLoadUAlphaRestPolynomial68, coeff_add, coeff_smul,
      coeff_eq_zero_of_natDegree_lt hc',
      coeff_eq_zero_of_natDegree_lt hcc,
      coeff_eq_zero_of_natDegree_lt hBc,
      coeff_eq_zero_of_natDegree_lt hC, zero_add, smul_eq_mul]
    ring
  have hVtop : Vtail.coeff (3 * n - g) =
      (1 / 2 : k) * delta * B.coeff (3 * n - g) := by
    have hcc : (((2 / 3 * gamma : k) • c).natDegree < 3 * n - g) :=
      (natDegree_smul_le _ c).trans_lt (hc.trans_lt (by omega))
    have hC : (C eta : k[X]).natDegree < 3 * n - g := by
      rw [natDegree_C]
      omega
    simp only [Vtail, coeff_add, coeff_smul,
      coeff_eq_zero_of_natDegree_lt hcc,
      coeff_eq_zero_of_natDegree_lt hC, zero_add, smul_eq_mul]
    ring
  have hCtop : C0c.coeff (4 * n) =
      (1 / 3 : k) * A.coeff (2 * n) ^ 2 := by
    have hp := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    rw [hi] at hp
    simp only [C0c, coeff_smul, smul_eq_mul, hp]
  have h1 := coeff_mul_derivative_at_bounds68 Ur Dtr
    (2 * n) (5 * n - g) (by omega) hUr hDtr
  have hi1 : 2 * n + (5 * n - g) - 1 = 12 * n - 4 * g - 1 := by omega
  rw [hi1, hUtop, hDtop] at h1
  have h5 := coeff_mul_derivative_at_bounds68 C0c Vtail
    (4 * n) (3 * n - g) (by omega) hC0c hVtail
  have hi5 : 4 * n + (3 * n - g) - 1 = 12 * n - 4 * g - 1 := by omega
  rw [hi5, hCtop, hVtop] at h5
  have h7 := coeff_mul_derivative_at_bounds68 Dtr Ur
    (5 * n - g) (2 * n) (by omega) hDtr hUr
  have hi7 : (5 * n - g) + 2 * n - 1 = 12 * n - 4 * g - 1 := by omega
  rw [hi7, hDtop, hUtop] at h7
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 4 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 4 * g - 1 :=
    fun p q hp hq => deepGap_natDegree_mul_derivative_lt68 p q u v
      (12 * n - 4 * g - 1) hv hp hq hu
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 4 * g - 1 :=
    hbound (4 * n - 2 * g) (6 * n - 2 * g) (by omega) (by omega)
      _ Er ((natDegree_smul_le _ c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 4 * g - 1 :=
    hbound (2 * n) (6 * n - 2 * g) (by omega) (by omega)
      _ Er ((natDegree_smul_le _ A).trans hA) hEr
  have heps : (C epsilon : k[X]).natDegree ≤ 0 := by rw [natDegree_C]
  have h4 : ((C epsilon : k[X]) * derivative Er).natDegree <
      12 * n - 4 * g - 1 :=
    hbound 0 (6 * n - 2 * g) (by omega) (by omega) _ Er heps hEr
  have h6 : (c * derivative Vr).natDegree < 12 * n - 4 * g - 1 :=
    hbound (4 * n - 2 * g) (6 * n - g) (by omega) (by omega)
      c Vr hc hVr
  simp only [coeff_add, coeff_sub, coeff_smul, h1, h5, h7,
    coeff_eq_zero_of_natDegree_lt h2,
    coeff_eq_zero_of_natDegree_lt h3,
    coeff_eq_zero_of_natDegree_lt h4,
    coeff_eq_zero_of_natDegree_lt h6, smul_eq_mul]
  have hcast2 : (((2 * n : ℕ) : k)) = 2 * (n : k) := by push_cast; rfl
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) = 5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 5 * n)]
    push_cast
    rfl
  rw [hcast2, hcast3, hcast5]
  ring

theorem laterDeepLowerOpenDoubleFiveWall_terminal_top_delta_classification68
    (N a b e delta : k) (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (packet : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      N a b 0 0 e delta) :
    e = (4 / 45 : k) * b ^ 2 ∧
      delta * a ^ 2 = (32 / 135 : k) * b ^ 3 ∧ delta ≠ 0 := by
  have hda : delta * a ^ 2 = (8 / 3 : k) * b * e := by
    have hp : N * a ^ 2 * (delta * a ^ 2 - (8 / 3 : k) * b * e) = 0 := by
      have ht := packet.rowZero
      simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
        sub_zero, add_zero] at ht
      linear_combination 9 * ht
    have hfac : N * a ^ 2 ≠ 0 := mul_ne_zero hN (pow_ne_zero 2 ha)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hfac)
  have heq : e = (4 / 45 : k) * b ^ 2 := by
    have hp : b * (e - (4 / 45 : k) * b ^ 2) = 0 := by
      have ht := packet.four
      simp only [mul_zero, zero_mul, zero_pow (by norm_num : 3 ≠ 0),
        add_zero] at ht
      linear_combination (3 / 10 : k) * ht - (3 / 40 : k) * hda
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hb)
  have hdeltaeq : delta * a ^ 2 = (32 / 135 : k) * b ^ 3 := by
    rw [heq] at hda
    linear_combination hda
  have hdeltane : delta ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hdeltaeq
    have hb3 : b ^ 3 = 0 := by
      have hp : (32 / 135 : k) * b ^ 3 = 0 := by linear_combination -hdeltaeq
      exact (mul_eq_zero.mp hp).resolve_left (by norm_num)
    exact hb (eq_zero_of_pow_eq_zero hb3)
  exact ⟨heq, hdeltaeq, hdeltane⟩

theorem laterDeepLowerOpenDoubleFiveWall_terminal_loaded_edges68
    (N G a b c₁ d₀ e delta : k)
    (hN : N ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hwall : 3 * G = 5 * N)
    (he : e = (4 / 45 : k) * b ^ 2)
    (hdelta : delta * a ^ 2 = (32 / 135 : k) * b ^ 3)
    (hi3 : (8 / 9 : k) * (-a * b * d₀ - b ^ 2 * c₁ + 3 * c₁ * e) =
      (1 / 2 : k) * delta * a * b)
    (hrow : (-4 / 27 : k) *
        (2 * a ^ 2 * b * d₀ * (5 * N - G) -
          6 * a * c₁ * e * (5 * N - G) -
          4 * N * a * b ^ 2 * c₁ -
          3 * b ^ 2 * e * (6 * N - 2 * G) -
          18 * e ^ 2 * (6 * N - 2 * G)) +
        (-1 / 6 : k) * delta * a ^ 2 * b * (3 * N - G) = 0) :
    a * c₁ = (-137 / 900 : k) * b ^ 2 ∧
      a ^ 2 * d₀ = (-293 / 13500 : k) * b ^ 3 := by
  have hG : G = (5 / 3 : k) * N := by
    linear_combination (1 / 3 : k) * hwall
  have hI := hi3
  rw [he] at hI
  have hInorm : b *
      (a ^ 2 * d₀ + (11 / 15 : k) * b * (a * c₁) +
        (2 / 15 : k) * b ^ 3) = 0 := by
    linear_combination
      (-9 / 8 : k) * a * hI - (9 / 16 : k) * b * hdelta
  have hR := hrow
  rw [hG, he] at hR
  have hRnorm : N *
      ((20 / 3 : k) * b * (a ^ 2 * d₀) -
        (52 / 9 : k) * b ^ 2 * (a * c₁) -
        (496 / 675 : k) * b ^ 4) = 0 := by
    linear_combination
      (-27 / 4 : k) * hR - (3 / 2 : k) * N * b * hdelta
  have hcprod : N * b ^ 2 *
      (a * c₁ - (-137 / 900 : k) * b ^ 2) = 0 := by
    linear_combination
      (-3 / 32 : k) * hRnorm + (5 / 8 : k) * N * hInorm
  have hfac : N * b ^ 2 ≠ 0 := mul_ne_zero hN (pow_ne_zero 2 hb)
  have hc : a * c₁ = (-137 / 900 : k) * b ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hcprod).resolve_left hfac)
  have hdprod : b * (a ^ 2 * d₀ - (-293 / 13500 : k) * b ^ 3) = 0 := by
    linear_combination
      hInorm - (11 / 15 : k) * b ^ 2 * hc
  have hd : a ^ 2 * d₀ = (-293 / 13500 : k) * b ^ 3 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hdprod).resolve_left hb)
  exact ⟨hc, hd⟩

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedTerminalLoadedPacket68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      2 * g ≤ h)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g = 5 * n)
    (hdegenerate :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0)
    (hcAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 4 * n - g)
    (hdAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - 2 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    let a := Ae.coeff (2 * n)
    let b := Be.coeff (3 * n - g)
    let c₁ := ce.coeff (4 * n - 2 * g)
    let d₀ := d.coeff 0
    let e := ee.coeff (6 * n - 2 * g)
    5 * n - 2 * g = g ∧
      ce.natDegree ≤ 4 * n - 2 * g ∧ d.natDegree ≤ 0 ∧
      (8 / 9 : k) * (-a * b * d₀ - b ^ 2 * c₁ + 3 * c₁ * e) =
        (1 / 2 : k) * delta * a * b ∧
      (-4 / 27 : k) *
          (2 * a ^ 2 * b * d₀ * ((5 * n - g : ℕ) : k) -
            6 * a * c₁ * e * ((5 * n - g : ℕ) : k) -
            4 * (n : k) * a * b ^ 2 * c₁ -
            3 * b ^ 2 * e * ((6 * n - 2 * g : ℕ) : k) -
            18 * e ^ 2 * ((6 * n - 2 * g : ℕ) : k)) +
          (-1 / 6 : k) * delta * a ^ 2 * b * ((3 * n - g : ℕ) : k) = 0 ∧
      e = (4 / 45 : k) * b ^ 2 ∧
      delta * a ^ 2 = (32 / 135 : k) * b ^ 3 ∧ delta ≠ 0 ∧
      a * c₁ = (-137 / 900 : k) * b ^ 2 ∧
      a ^ 2 * d₀ = (-293 / 13500 : k) * b ^ 3 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let c₁ := ce.coeff (4 * n - 2 * g)
  let d₀ := d.coeff 0
  let e := ee.coeff (6 * n - 2 * g)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change 60 ∣ 4 * n - g at hcAlign
  change 60 ∣ 5 * n - 2 * g at hdAlign
  have terminalData :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedTerminalLoad68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hcAlign)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdAlign)
  change 5 * n - 2 * g = g ∧
      ce.natDegree ≤ 4 * n - g - (5 * n - 2 * g) ∧
      d.natDegree ≤ 0 ∧
      (8 / 9 : k) *
        (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) * d.coeff 0) -
          Be.coeff (3 * n - g) ^ 2 *
            ce.coeff (4 * n - g - (5 * n - 2 * g)) +
          3 * ce.coeff (4 * n - g - (5 * n - 2 * g)) *
            ee.coeff (6 * n - 2 * g)) =
        (1 / 2 : k) * delta * Ae.coeff (2 * n) * Be.coeff (3 * n - g)
    at terminalData
  have hc : ce.natDegree ≤ 4 * n - 2 * g := by
    exact terminalData.2.1.trans (by omega)
  have hd : d.natDegree ≤ 0 := terminalData.2.2.1
  have hi3scalar :
      (8 / 9 : k) * (-a * b * d₀ - b ^ 2 * c₁ + 3 * c₁ * e) =
        (1 / 2 : k) * delta * a * b := by
    dsimp only [a, b, c₁, d₀, e]
    simpa only [show 4 * n - g - (5 * n - 2 * g) =
      4 * n - 2 * g by omega, neg_mul] using terminalData.2.2.2
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _
    at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have ha : a ≠ 0 := by
    dsimp only [a]
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ ∧ LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      (n : k) (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) delta at selector
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have topPacket : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      (n : k) a b 0 0 e delta := by
    dsimp only [a, b, e]
    simpa only [hdegenerate.1, hdegenerate.2.2.1] using selector.2.2
  have topClass := laterDeepLowerOpenDoubleFiveWall_terminal_top_delta_classification68
    (n : k) a b e delta (Nat.cast_ne_zero.mpr hn.ne') ha
    hdegenerate.2.1 topPacket
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowPoly : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at hr
    exact polynomialSecondaryResidualRowOne68
      0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee hr
  have hrowCoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 4 * g - 1)) hrowPoly
  rw [coeff_add, coeff_zero,
    secondaryResidualRowOnePolynomial68_coeff_terminal_aligned_fiveWall
      Ae Be ce d ee n g hn hopen hwall hA secondary.2.1 hc hd he2,
    cubicLoadRowOnePolynomial68_coeff_terminal_aligned_fiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce d ee n g hn hopen hwall
      hA secondary.2.1 hc hd he2] at hrowCoeff
  have hrowScalar :
      (-4 / 27 : k) *
          (2 * a ^ 2 * b * d₀ * ((5 * n - g : ℕ) : k) -
            6 * a * c₁ * e * ((5 * n - g : ℕ) : k) -
            4 * (n : k) * a * b ^ 2 * c₁ -
            3 * b ^ 2 * e * ((6 * n - 2 * g : ℕ) : k) -
            18 * e ^ 2 * ((6 * n - 2 * g : ℕ) : k)) +
          (-1 / 6 : k) * delta * a ^ 2 * b * ((3 * n - g : ℕ) : k) = 0 := by
    simpa only [a, b, c₁, d₀, e] using hrowCoeff
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - g : ℕ) : k)) =
      5 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  have hrowField := hrowScalar
  rw [hcast3, hcast5, hcast6] at hrowField
  have hw : (3 : k) * (g : k) = 5 * (n : k) := by exact_mod_cast hwall
  have edges := laterDeepLowerOpenDoubleFiveWall_terminal_loaded_edges68
    (n : k) (g : k) a b c₁ d₀ e delta
    (Nat.cast_ne_zero.mpr hn.ne') ha hdegenerate.2.1 hw
    topClass.1 topClass.2.1 hi3scalar hrowField
  exact ⟨terminalData.1, hc, hd, hi3scalar, hrowScalar,
    topClass.1, topClass.2.1, topClass.2.2, edges.1, edges.2⟩

#print axioms secondaryResidualRowOnePolynomial68_coeff_terminal_aligned_fiveWall
#print axioms cubicLoadRowOnePolynomial68_coeff_terminal_aligned_fiveWall
#print axioms laterDeepLowerOpenDoubleFiveWall_terminal_top_delta_classification68
#print axioms laterDeepLowerOpenDoubleFiveWall_terminal_loaded_edges68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedTerminalLoadedPacket68

end LaterDeepLowerOpenDoubleFiveWallAlignedTerminalLoadedSource68

end Max11DegreeRoutes
