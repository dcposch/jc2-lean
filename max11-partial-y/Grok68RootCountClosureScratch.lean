import Grok68DivisorBridgeScratch

/-! # Root-count closure of the terminal `κ = 0` subcase

On the wall `9N = 7S` the landed divisor bridge supplies the squarefree
divisor `B`, the nonzero fibre constant `C0 = 81 ε γ + 27 i₃`, the
exact identities `C0 v - C(4κ) = B q` and `36 d² - C C0 = B s`, the
profile `W = 4A + 3v²`, and
`B ∣ B' d L + C(108 terminal)` for
`L = v (W² - C(72γ)) + 48 d`.  Clearing the fibre against
`c₁ = 162 terminal / C0` rewrites the bridge, at every simple root, as
the equivalent vanishing of `B' L + 24 c₁ d`.

If `κ = 0` then `v` itself vanishes on the zero set of `B`, so `L = 48 d`
there and `B'` evaluates to the same nonzero scalar
`-108 terminal / (48 δ)` at all `3m` distinct roots of `B`.  The
polynomial `B' - C(const)` therefore has `3m` distinct roots and degree
`3m - 1`, hence is zero (`Polynomial.card_roots` together with
`natDegree_derivative`), contradicting `deg B = 3m ≥ 3`.  This subcase
closes completely.

In the complementary case the same root identities assemble the
ODE-shaped congruence
`C0 W' + 6 B' d (W² + 6 v₀² W - 72 γ) ≡ 0 (mod B)`
of exact degree `21m - 1`.  A full contradiction for `κ ≠ 0` would
need an ODE-rigidity descent beyond composing these identities; that
step is recorded as a residual, not claimed.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootCountClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Wall scale `N = 7m`, `S = 9m` -/

/-- Coprimality of `7` and `9` realises the wall as an integral scale
`m ≥ 1` with the recorded degree dictionary. -/
theorem fiveToSix_qZero_terminal_wall_scale_algebra68
    (N S : ℕ) (hN : 0 < N) (hEq : 9 * N = 7 * S) :
    ∃ m : ℕ, 0 < m ∧ N = 7 * m ∧ S = 9 * m ∧
      3 * N - 2 * S = 3 * m ∧
      5 * N - 3 * S = 8 * m ∧
      2 * N - S = 5 * m ∧
      N + 2 * (2 * N - S) = 17 * m ∧
      12 * N - 7 * S - 1 = 21 * m - 1 ∧
      3 ≤ 3 * m := by
  have h7 : 7 ∣ 9 * N := by
    rw [hEq]
    exact dvd_mul_right 7 S
  have hcop : Nat.Coprime 7 9 := by decide
  have hN7 : 7 ∣ N := hcop.dvd_of_dvd_mul_left h7
  obtain ⟨m, hm⟩ := hN7
  have hmpos : 0 < m := by
    rw [hm] at hN
    omega
  have hS : S = 9 * m := by
    have hmul : 7 * S = 9 * (7 * m) := by
      rw [← hEq, hm]
    have : 7 * S = 7 * (9 * m) := by
      rw [hmul]
      ring
    exact Nat.mul_left_cancel (by norm_num : 0 < 7) this
  refine ⟨m, hmpos, hm, hS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-! ## Scalar remainder of `v` and the square fibre -/

/-- On the zero set of `B`, the congruence `C0 v - C(4κ) = B q` pins
`v` to the scalar `v₀ = 4κ / C0`. -/
theorem fiveToSix_qZero_terminal_v0_eval_algebra68
    (C0 kappa : k) (B v q : k[X]) (x : k)
    (hC0 : C0 ≠ 0)
    (hBx : B.eval x = 0)
    (hBq : (C0 : k) • v - C (4 * kappa) = B * q) :
    v.eval x = 4 * kappa / C0 := by
  have h := congrArg (fun R : k[X] => R.eval x) hBq
  simp only [eval_sub, eval_smul, eval_C, eval_mul, smul_eq_mul] at h
  rw [hBx, zero_mul, sub_eq_zero] at h
  exact eq_div_of_mul_eq hC0 (by linear_combination h)

/-- On the zero set of `B`, the congruence `36 d² - C C0 = B s` pins
`d²` to the scalar `δ = C0 / 36`. -/
theorem fiveToSix_qZero_terminal_delta_eval_algebra68
    (C0 : k) (B d s : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hsq : (36 : k) • d ^ 2 - C C0 = B * s) :
    d.eval x ^ 2 = C0 / 36 := by
  have h := congrArg (fun R : k[X] => R.eval x) hsq
  simp only [eval_sub, eval_smul, eval_mul, eval_pow, eval_C,
    smul_eq_mul] at h
  rw [hBx, zero_mul, sub_eq_zero] at h
  exact eq_div_of_mul_eq (by norm_num : (36 : k) ≠ 0)
    (by linear_combination h)

/-- The clearing identity `24 c₁ δ = 108 terminal`. -/
theorem fiveToSix_qZero_terminal_c1_delta_mul_algebra68
    (terminal C0 : k) (hC0 : C0 ≠ 0) :
    let c1 := (162 : k) * terminal / C0
    let delta := C0 / 36
    (24 : k) * c1 * delta = 108 * terminal := by
  intro c1 delta
  dsimp only [c1, delta]
  field_simp [hC0]
  ring

/-! ## Cleared bridge, equivalent to the landed face at simple roots -/

/-- At a simple root, `d (B' L + 24 c₁ d)` equals the landed face plus
`24 c₁ (d² - δ)`.  Coprimeness of `B` and `d` cancels `d`. -/
theorem fiveToSix_qZero_terminal_cleared_bridge_eval_algebra68
    (terminal C0 c1 delta : k) (d L : k[X]) (x : k) (Bp : k)
    (hdx : d.eval x ≠ 0)
    (hC0 : C0 ≠ 0)
    (hc1 : c1 = (162 : k) * terminal / C0)
    (hdelta : delta = C0 / 36)
    (hsq : d.eval x ^ 2 = delta)
    (hface : Bp * d.eval x * L.eval x = -108 * terminal) :
    Bp * L.eval x + 24 * c1 * d.eval x = 0 := by
  have hid : (24 : k) * c1 * delta = 108 * terminal := by
    rw [hc1, hdelta]
    field_simp [hC0]
    ring
  have hface0 : Bp * d.eval x * L.eval x + 108 * terminal = 0 := by
    linear_combination hface
  have hsq0 : d.eval x ^ 2 - delta = 0 := by
    linear_combination hsq
  have hprod : d.eval x *
      (Bp * L.eval x + 24 * c1 * d.eval x) = 0 := by
    linear_combination hface0 + (24 * c1) * hsq0 + hid
  exact (mul_eq_zero.mp hprod).resolve_left hdx

/-! ## Derivative congruences at simple roots -/

/-- Combining `C0 v' = B' q`, `q = -v T`, and `T = 6 W d` yields
`C0 v' = -6 v₀ B' W d` on the zero set of `B`. -/
theorem fiveToSix_qZero_terminal_v'_congruence_eval_algebra68
    (C0 v0 : k) (d v W T q : k[X]) (x : k) (Bp : k)
    (hv : v.eval x = v0)
    (hv' : C0 * (derivative v).eval x = Bp * q.eval x)
    (hq : q.eval x = -v.eval x * T.eval x)
    (hT : T.eval x = 6 * W.eval x * d.eval x) :
    C0 * (derivative v).eval x =
      -6 * v0 * Bp * W.eval x * d.eval x := by
  have h1 : C0 * (derivative v).eval x +
      Bp * v.eval x * T.eval x = 0 := by
    linear_combination hv' + Bp * hq
  have h2 : C0 * (derivative v).eval x +
      6 * Bp * v.eval x * W.eval x * d.eval x = 0 := by
    rw [hT] at h1
    linear_combination h1
  rw [hv] at h2
  linear_combination h2

/-- Combining `72 d d' = B' s`, `s = T`, and `T = 6 W d` yields
`12 d' = B' W` on the zero set of `B`. -/
theorem fiveToSix_qZero_terminal_d'_congruence_eval_algebra68
    (d W T s : k[X]) (x : k) (Bp : k)
    (hdx : d.eval x ≠ 0)
    (hd' : (72 : k) * d.eval x * (derivative d).eval x =
      Bp * s.eval x)
    (hs : s.eval x = T.eval x)
    (hT : T.eval x = 6 * W.eval x * d.eval x) :
    (12 : k) * (derivative d).eval x = Bp * W.eval x := by
  have h1 : 72 * d.eval x * (derivative d).eval x -
      6 * Bp * W.eval x * d.eval x = 0 := by
    rw [hs, hT] at hd'
    linear_combination hd'
  have hprod : d.eval x *
      (72 * (derivative d).eval x - 6 * Bp * W.eval x) = 0 := by
    linear_combination h1
  have h72 : 72 * (derivative d).eval x - 6 * Bp * W.eval x = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hdx
  linear_combination (1 / 6 : k) * h72

/-- Differentiating the exact profile `W = 4A + 3v²`. -/
theorem fiveToSix_qZero_terminal_W_derivative_algebra68
    (A v W : k[X])
    (hW : W = (4 : k) • A + (3 : k) • v ^ 2) :
    derivative W =
      (4 : k) • derivative A + (6 : k) • (v * derivative v) := by
  have hv2 : derivative (v ^ 2) = C (2 : k) * (v * derivative v) := by
    rw [pow_two, derivative_mul, map_ofNat]
    ring
  have h32 : C (3 : k) * C (2 : k) = C (6 : k) := by
    rw [← C_mul]
    norm_num
  rw [hW, derivative_add, derivative_smul, derivative_smul, hv2]
  simp only [Polynomial.smul_eq_C_mul]
  rw [← mul_assoc (C (3 : k)), h32]

/-- Evaluation of the differentiated profile. -/
theorem fiveToSix_qZero_terminal_W'_eval_algebra68
    (A v W : k[X]) (x : k)
    (hW : W = (4 : k) • A + (3 : k) • v ^ 2) :
    (derivative W).eval x =
      4 * (derivative A).eval x +
        6 * v.eval x * (derivative v).eval x := by
  have h := congrArg (fun R : k[X] => R.eval x)
    (fiveToSix_qZero_terminal_W_derivative_algebra68 A v W hW)
  simp only [eval_add, eval_smul, eval_mul, smul_eq_mul] at h
  linear_combination h

/-! ## ODE-shaped identity at a simple root -/

/-- Row one together with the derivative congruences
`C0 v' = -6 v₀ B' W d` and `12 d' = B' W` produce the ODE face
`C0 W' + 6 B' d (W² + 6 v₀² W - 72 γ) = 0`. -/
theorem fiveToSix_qZero_terminal_ode_eval_algebra68
    (gamma C0 v0 : k) (A d v W : k[X]) (x : k) (Bp : k)
    (hdx : d.eval x ≠ 0)
    (hWev : W.eval x = 4 * A.eval x + 3 * v.eval x ^ 2)
    (hW'ev : (derivative W).eval x =
      4 * (derivative A).eval x +
        6 * v.eval x * (derivative v).eval x)
    (hv : v.eval x = v0)
    (hsq : (36 : k) * d.eval x ^ 2 = C0)
    (hv' : C0 * (derivative v).eval x =
      -6 * v0 * Bp * W.eval x * d.eval x)
    (hd' : (12 : k) * (derivative d).eval x = Bp * W.eval x)
    (hrow : Bp * (A.eval x * W.eval x - 18 * gamma) +
      6 * (derivative A).eval x * d.eval x -
      9 * d.eval x * v.eval x * (derivative v).eval x -
      9 * (derivative d).eval x * v.eval x ^ 2 = 0) :
    C0 * (derivative W).eval x +
      6 * Bp * d.eval x *
        (W.eval x ^ 2 + 6 * v0 ^ 2 * W.eval x - 72 * gamma) = 0 := by
  have hd12 : 12 * (derivative d).eval x - Bp * W.eval x = 0 := by
    linear_combination hd'
  have hv6 : 6 * d.eval x * (derivative v).eval x +
      Bp * v0 * W.eval x = 0 := by
    have hprod : 6 * d.eval x *
        (6 * d.eval x * (derivative v).eval x +
          Bp * v0 * W.eval x) = 0 := by
      linear_combination hv' + (derivative v).eval x * hsq
    exact (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (by norm_num) hdx)
  have hrowW : Bp * (A.eval x * W.eval x - 18 * gamma) +
      6 * (derivative A).eval x * d.eval x +
      (3 / 4 : k) * Bp * v0 ^ 2 * W.eval x = 0 := by
    rw [hv] at hrow
    linear_combination hrow + (3 / 2 : k) * v0 * hv6 +
      (3 / 4 : k) * v0 ^ 2 * hd12
  have hrow4 : 4 * Bp * (A.eval x * W.eval x - 18 * gamma) +
      24 * (derivative A).eval x * d.eval x +
      3 * Bp * v0 ^ 2 * W.eval x = 0 := by
    linear_combination (4 : k) * hrowW
  have hWev0 : W.eval x = 4 * A.eval x + 3 * v0 ^ 2 := by
    rw [← hv]
    exact hWev
  have hrowA : Bp * (W.eval x ^ 2 - 72 * gamma) +
      24 * (derivative A).eval x * d.eval x = 0 := by
    linear_combination hrow4 + (Bp * W.eval x) * hWev0
  have hsq0 : (36 : k) * d.eval x ^ 2 - C0 = 0 := by
    linear_combination hsq
  have hA'C : 4 * C0 * (derivative A).eval x +
      6 * Bp * d.eval x * (W.eval x ^ 2 - 72 * gamma) = 0 := by
    linear_combination (6 * d.eval x) * hrowA -
      (4 * (derivative A).eval x) * hsq0
  have hW'ev0 : (derivative W).eval x =
      4 * (derivative A).eval x +
        6 * v0 * (derivative v).eval x := by
    rw [← hv]
    exact hW'ev
  have hW'C : C0 * (derivative W).eval x -
      4 * C0 * (derivative A).eval x -
      6 * C0 * v0 * (derivative v).eval x = 0 := by
    linear_combination C0 * hW'ev0
  have hvC : 6 * C0 * v0 * (derivative v).eval x +
      36 * v0 ^ 2 * Bp * W.eval x * d.eval x = 0 := by
    linear_combination (6 * v0) * hv'
  linear_combination hW'C + hA'C + hvC

/-! ## Degree of the ODE polynomial -/

/-- Exact degree and top coefficient of
`Q = W² + C(6 v₀²) W - C(72 γ)` on the wall. -/
theorem fiveToSix_qZero_terminal_ode_Q_degree_algebra68
    (gamma v0 : k) (W : k[X]) (N S : ℕ)
    (hN : 0 < N) (hS : 0 < S) (hEq : 9 * N = 7 * S)
    (hWdeg : W.natDegree = 2 * N - S)
    (hWtop : W.coeff (2 * N - S) ≠ 0) :
    let R := 2 * N - S
    let Q := W ^ 2 + C (6 * v0 ^ 2) * W - C (72 * gamma)
    Q.natDegree = 2 * R ∧ Q.coeff (2 * R) = W.coeff R ^ 2 := by
  let R := 2 * N - S
  let Q := W ^ 2 + C (6 * v0 ^ 2) * W - C (72 * gamma)
  change Q.natDegree = 2 * R ∧ Q.coeff (2 * R) = W.coeff R ^ 2
  have hRpos : 0 < R := by dsimp only [R]; omega
  have hWne : W ≠ 0 := by
    intro hz
    apply hWtop
    rw [hz, coeff_zero]
  have hW2deg : (W ^ 2).natDegree = 2 * R := by
    rw [natDegree_pow, hWdeg]
  have hW2ne : W ^ 2 ≠ 0 := pow_ne_zero 2 hWne
  have hCWdeg : (C (6 * v0 ^ 2) * W).natDegree ≤ R := by
    compute_degree
    omega
  have hCdeg : (C (72 * gamma) : k[X]).natDegree = 0 := natDegree_C _
  have hlow1 : (C (6 * v0 ^ 2) * W).natDegree < (W ^ 2).natDegree := by
    rw [hW2deg]
    exact lt_of_le_of_lt hCWdeg (by omega)
  have hsumdeg : (W ^ 2 + C (6 * v0 ^ 2) * W).natDegree = 2 * R := by
    rw [natDegree_add_eq_left_of_natDegree_lt hlow1, hW2deg]
  have hlow2 : (C (72 * gamma) : k[X]).natDegree <
      (W ^ 2 + C (6 * v0 ^ 2) * W).natDegree := by
    rw [hsumdeg, hCdeg]
    omega
  have hQdeg : Q.natDegree = 2 * R := by
    dsimp only [Q]
    rw [natDegree_sub_eq_left_of_natDegree_lt hlow2, hsumdeg]
  have hW2coeff : (W ^ 2).coeff (2 * R) = W.coeff R ^ 2 := by
    have h := coeff_pow_at_bound68 W R 2 hWdeg.le
    simpa only [pow_two, Nat.mul_comm] using h
  have hCWcoeff : (C (6 * v0 ^ 2) * W).coeff (2 * R) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hCWdeg (by omega))
  have hCcoeff : (C (72 * gamma) : k[X]).coeff (2 * R) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [hCdeg]; omega)
  have hQcoeff : Q.coeff (2 * R) = W.coeff R ^ 2 := by
    dsimp only [Q]
    rw [coeff_sub, coeff_add, hW2coeff, hCWcoeff, hCcoeff]
    ring
  exact ⟨hQdeg, hQcoeff⟩

/-- Exact degree and top coefficient of the ODE polynomial
`C0 W' + 6 B' d Q` on the wall: degree `12N - 7S - 1 = 3N - 1`. -/
theorem fiveToSix_qZero_terminal_ode_degree_algebra68
    (gamma v0 C0 : k) (B d W : k[X]) (N S : ℕ)
    (hN : 0 < N) (hS : 0 < S) (hEq : 9 * N = 7 * S)
    (hBdeg : B.natDegree = 3 * N - 2 * S)
    (hddeg : d.natDegree = 5 * N - 3 * S)
    (hWdeg : W.natDegree = 2 * N - S)
    (hBtop : B.coeff (3 * N - 2 * S) ≠ 0)
    (hdtop : d.coeff (5 * N - 3 * S) ≠ 0)
    (hWtop : W.coeff (2 * N - S) ≠ 0)
    (hC0 : C0 ≠ 0) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let R := 2 * N - S
    let Q := W ^ 2 + C (6 * v0 ^ 2) * W - C (72 * gamma)
    let P := C0 • derivative W +
      (6 : k) • (derivative B * d * Q)
    Q.natDegree = 2 * R ∧
      Q.coeff (2 * R) = W.coeff R ^ 2 ∧
      P.natDegree = 12 * N - 7 * S - 1 ∧
      P.coeff (12 * N - 7 * S - 1) =
        (6 : k) * B.coeff D * (D : k) * d.coeff V *
          W.coeff R ^ 2 ∧
      12 * N - 7 * S - 1 = 3 * N - 1 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let R := 2 * N - S
  let Q := W ^ 2 + C (6 * v0 ^ 2) * W - C (72 * gamma)
  let P := C0 • derivative W +
    (6 : k) • (derivative B * d * Q)
  change Q.natDegree = 2 * R ∧
    Q.coeff (2 * R) = W.coeff R ^ 2 ∧
    P.natDegree = 12 * N - 7 * S - 1 ∧
    P.coeff (12 * N - 7 * S - 1) =
      (6 : k) * B.coeff D * (D : k) * d.coeff V *
        W.coeff R ^ 2 ∧
    12 * N - 7 * S - 1 = 3 * N - 1
  have hDpos : 0 < D := by dsimp only [D]; omega
  have hRpos : 0 < R := by dsimp only [R]; omega
  have hwall : 12 * N - 7 * S - 1 = 3 * N - 1 := by omega
  have hidx : D - 1 + V + 2 * R = 12 * N - 7 * S - 1 := by
    dsimp only [D, V, R]
    omega
  have hQ := fiveToSix_qZero_terminal_ode_Q_degree_algebra68
    gamma v0 W N S hN hS hEq hWdeg hWtop
  have hQdeg : Q.natDegree = 2 * R := hQ.1
  have hQcoeff : Q.coeff (2 * R) = W.coeff R ^ 2 := hQ.2
  have hQtop : Q.coeff (2 * R) ≠ 0 := by
    rw [hQcoeff]
    exact pow_ne_zero 2 hWtop
  have hQne : Q ≠ 0 := by
    intro hz
    apply hQtop
    rw [hz, coeff_zero]
  have hB'le : (derivative B).natDegree ≤ D - 1 :=
    (natDegree_derivative_le B).trans (by rw [hBdeg])
  have hB'coeff : (derivative B).coeff (D - 1) = B.coeff D * (D : k) :=
    coeff_derivative_at_bound68 B D hDpos
  have hDcast : (D : k) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hB'top : (derivative B).coeff (D - 1) ≠ 0 := by
    rw [hB'coeff]
    exact mul_ne_zero hBtop hDcast
  have hB'deg : (derivative B).natDegree = D - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hB'le hB'top
  have hB'ne : derivative B ≠ 0 := by
    intro hz
    apply hB'top
    rw [hz, coeff_zero]
  have hdne : d ≠ 0 := by
    intro hz
    apply hdtop
    rw [hz, coeff_zero]
  have hBdne : derivative B * d ≠ 0 := mul_ne_zero hB'ne hdne
  have hBddeg : (derivative B * d).natDegree = D - 1 + V := by
    rw [natDegree_mul hB'ne hdne, hB'deg, hddeg]
  have hBdQdeg : (derivative B * d * Q).natDegree =
      12 * N - 7 * S - 1 := by
    rw [natDegree_mul hBdne hQne, hBddeg, hQdeg, hidx]
  have hBdcoeff : (derivative B * d).coeff (D - 1 + V) =
      B.coeff D * (D : k) * d.coeff V := by
    have h := coeff_mul_at_bounds68 (derivative B) d (D - 1) V
      hB'deg.le hddeg.le
    rw [hB'coeff] at h
    simpa only [mul_assoc] using h
  have hBdQcoeff : (derivative B * d * Q).coeff (12 * N - 7 * S - 1) =
      B.coeff D * (D : k) * d.coeff V * W.coeff R ^ 2 := by
    have h := coeff_mul_at_bounds68 (derivative B * d) Q (D - 1 + V)
      (2 * R) hBddeg.le hQdeg.le
    rw [show D - 1 + V + 2 * R = 12 * N - 7 * S - 1 from hidx] at h
    rw [hBdcoeff, hQcoeff] at h
    simpa only [mul_assoc] using h
  have h6ne : (6 : k) ≠ 0 := by norm_num
  have hRight : ((6 : k) • (derivative B * d * Q)).natDegree =
      12 * N - 7 * S - 1 := by
    rw [natDegree_smul _ h6ne, hBdQdeg]
  have hRightcoeff :
      ((6 : k) • (derivative B * d * Q)).coeff (12 * N - 7 * S - 1) =
        (6 : k) * B.coeff D * (D : k) * d.coeff V *
          W.coeff R ^ 2 := by
    rw [coeff_smul, hBdQcoeff, smul_eq_mul]
    ring
  have hWne : W ≠ 0 := by
    intro hz
    apply hWtop
    rw [hz, coeff_zero]
  have hWdegpos : 0 < W.natDegree := by rw [hWdeg]; omega
  have hW'ne : derivative W ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hWdegpos)
  have hW'deg : (derivative W).natDegree = R - 1 := by
    have : (derivative W).natDegree = W.natDegree - 1 :=
      natDegree_derivative W
    rwa [hWdeg] at this
  have hLeft : (C0 • derivative W).natDegree = R - 1 := by
    rw [natDegree_smul _ hC0, hW'deg]
  have hlow : (C0 • derivative W).natDegree <
      ((6 : k) • (derivative B * d * Q)).natDegree := by
    rw [hLeft, hRight]
    dsimp only [R]
    omega
  have hPdeg : P.natDegree = 12 * N - 7 * S - 1 := by
    dsimp only [P]
    rw [natDegree_add_eq_right_of_natDegree_lt hlow, hRight]
  have hlow' : (C0 • derivative W).natDegree < 12 * N - 7 * S - 1 := by
    rwa [hRight] at hlow
  have hLeftcoeff : (C0 • derivative W).coeff (12 * N - 7 * S - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow'
  have hPcoeff : P.coeff (12 * N - 7 * S - 1) =
      (6 : k) * B.coeff D * (D : k) * d.coeff V *
        W.coeff R ^ 2 := by
    dsimp only [P]
    rw [coeff_add, hLeftcoeff, hRightcoeff, zero_add]
  exact ⟨hQdeg, hQcoeff, hPdeg, hPcoeff, hwall⟩

/-! ## Kappa-zero face and the root-count contradiction -/

/-- If `κ = 0` then `v₀ = 0`, so `L` evaluates to `48 d` on the zero
set of `B`. -/
theorem fiveToSix_qZero_terminal_kappa_zero_L_eval_algebra68
    (gamma : k) (d v W L : k[X]) (x : k)
    (hv : v.eval x = 0)
    (hL : L = v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d) :
    L.eval x = 48 * d.eval x := by
  have hLev := fiveToSix_qZero_terminal_L_eval_algebra68
    gamma d v W L x hL
  rw [hLev, hv]
  ring

/-- The bridge face with `L = 48 d` and `d² = δ` forces `B'` to the
scalar `-108 terminal / (48 δ)` at the root. -/
theorem fiveToSix_qZero_terminal_kappa_zero_derivative_eval_algebra68
    (terminal delta : k) (d L : k[X]) (x : k) (Bp : k)
    (hdelta : delta ≠ 0)
    (hsq : d.eval x ^ 2 = delta)
    (hL : L.eval x = 48 * d.eval x)
    (hface : Bp * d.eval x * L.eval x = -108 * terminal) :
    Bp = -108 * terminal / (48 * delta) := by
  have hden : (48 : k) * delta ≠ 0 :=
    mul_ne_zero (by norm_num) hdelta
  have h1 : Bp * d.eval x * (48 * d.eval x) = -108 * terminal := by
    rw [← hL]
    exact hface
  have h2 : Bp * (48 * d.eval x ^ 2) = -108 * terminal := by
    convert h1 using 1
    ring
  rw [hsq] at h2
  exact eq_div_of_mul_eq hden h2

/-- Squarefreeness makes the roots of `B` simple, so they are pairwise
distinct and `B.roots` is nodup. -/
theorem fiveToSix_qZero_terminal_squarefree_roots_nodup_algebra68
    {B : k[X]} (hB : B ≠ 0)
    (hsf : IsCoprime B (derivative B)) :
    B.roots.Nodup := by
  classical
  have hsimple : ∀ a : k, B.eval a = 0 →
      (derivative B).eval a ≠ 0 := by
    intro a ha
    have hx :=
      (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (k := k) k B (derivative B)).mp hsf a
    rw [aeval_def, aeval_def] at hx
    exact hx.resolve_left (not_ne_iff.mpr ha)
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [count_roots]
  by_cases ha : B.eval a = 0
  · have hpos : 0 < B.rootMultiplicity a :=
      (rootMultiplicity_pos hB).mpr ha
    have hnot : ¬ 1 < B.rootMultiplicity a := by
      intro hlt
      have hboth := (one_lt_rootMultiplicity_iff_isRoot hB).mp hlt
      exact hsimple a ha (IsRoot.eq_zero hboth.2)
    omega
  · have hz : B.rootMultiplicity a = 0 :=
      rootMultiplicity_eq_zero ha
    simp [hz]

/-- If `B'` evaluates to a single scalar at every root of a squarefree
polynomial of degree at least `3`, then `B' - C(const)` has as many
distinct roots as `B` but strictly smaller degree, hence vanishes, so
`B'` is constant, contradicting `natDegree_derivative`. -/
theorem fiveToSix_qZero_terminal_constant_on_simple_roots_impossible_algebra68
    {B : k[X]} (c : k)
    (hB : B ≠ 0)
    (hsf : IsCoprime B (derivative B))
    (hdeg : 3 ≤ B.natDegree)
    (hroot : ∀ x : k, B.eval x = 0 → (derivative B).eval x = c) :
    False := by
  classical
  let P := derivative B - C c
  have hB'deg : (derivative B).natDegree = B.natDegree - 1 :=
    natDegree_derivative B
  have hB'degge : 2 ≤ (derivative B).natDegree := by
    rw [hB'deg]
    omega
  have hP0false : P = 0 → False := by
    intro hP0
    have hB'c : derivative B = C c := sub_eq_zero.mp hP0
    by_cases hc0 : c = 0
    · have hB'0 : derivative B = 0 := by
        rw [hB'c, hc0, C_0]
      have : B.natDegree = 0 := derivative_eq_zero.mp hB'0
      omega
    · have : (derivative B).natDegree = 0 := by
        rw [hB'c, natDegree_C]
      omega
  by_cases hP0 : P = 0
  · exact hP0false hP0
  · have hnodup :=
      fiveToSix_qZero_terminal_squarefree_roots_nodup_algebra68 hB hsf
    have hsubset : B.roots.toFinset ⊆ P.roots.toFinset := by
      intro x hx
      have hxB : x ∈ B.roots := Multiset.mem_toFinset.mp hx
      have hBx : B.eval x = 0 := (mem_roots hB).mp hxB
      have hPev : P.eval x = 0 := by
        simp only [P, eval_sub, eval_C]
        rw [hroot x hBx, sub_self]
      exact Multiset.mem_toFinset.mpr ((mem_roots hP0).mpr hPev)
    have hle := Finset.card_le_card hsubset
    have hBfin : B.roots.toFinset.card = B.roots.card :=
      Multiset.toFinset_card_of_nodup hnodup
    have hPfin : P.roots.toFinset.card ≤ P.roots.card :=
      Multiset.toFinset_card_le _
    have hBcard : B.roots.card = B.natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    have hPcardWB : (P.roots.card : WithBot ℕ) ≤ P.degree :=
      Polynomial.card_roots hP0
    have hPcard : P.roots.card ≤ P.natDegree :=
      WithBot.coe_le_coe.1
        (hPcardWB.trans (le_of_eq (degree_eq_natDegree hP0)))
    have hPdeg : P.natDegree ≤ B.natDegree - 1 := by
      have hsub := natDegree_sub_le (derivative B) (C c)
      have hmax : max (derivative B).natDegree (C c : k[X]).natDegree ≤
          B.natDegree - 1 := by
        rw [hB'deg, natDegree_C]
        exact max_le le_rfl (Nat.zero_le _)
      exact hsub.trans hmax
    have : B.natDegree ≤ P.natDegree := by
      calc
        B.natDegree = B.roots.card := hBcard.symm
        _ = B.roots.toFinset.card := hBfin.symm
        _ ≤ P.roots.toFinset.card := hle
        _ ≤ P.roots.card := hPfin
        _ ≤ P.natDegree := hPcard
    omega

/-! ## Source-facing assembly -/

/-- Source-facing assembly: the terminal first-integral remainder `κ`
is nonzero (the vanishing subcase is closed by a root-count against
`deg B = 3m ≥ 3`), the landed bridge is equivalent at simple roots to
the cleared divisor `B ∣ B' L + C(24 c₁) d`, and the complementary
`κ ≠ 0` branch carries the ODE congruence
`B ∣ C0 W' + 6 B' d (W² + C(6 v₀²) W - C(72 γ))` of exact degree
`21m - 1`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_root_count_closure68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let R := 2 * N - S
    ∃ i3 kappa : k, ∃ v W T q L : k[X],
      let C0 := 81 * epsilon * gamma + 27 * i3
      let v0 := (4 * kappa) / C0
      let c1 := (162 : k) * terminal / C0
      let delta := C0 / 36
      let Q := W ^ 2 + C (6 * v0 ^ 2) * W - C (72 * gamma)
      let P := C0 • derivative W +
        (6 : k) • (derivative B * d * Q)
      C0 ≠ 0 ∧
      kappa ≠ 0 ∧
      W = (4 : k) • A + (3 : k) • v ^ 2 ∧
      L = v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d ∧
      (C0 : k) • v - C (4 * kappa) = B * q ∧
      IsCoprime B (derivative B) ∧
      (∀ x : k, B.eval x = 0 →
        v.eval x = v0 ∧
          d.eval x ^ 2 = delta ∧
          (derivative B).eval x * L.eval x +
            24 * c1 * d.eval x = 0 ∧
          C0 * (derivative W).eval x +
            6 * (derivative B).eval x * d.eval x *
              (W.eval x ^ 2 + 6 * v0 ^ 2 * W.eval x - 72 * gamma) =
            0) ∧
      B ∣ derivative B * L + C (24 * c1) * d ∧
      B ∣ P ∧
      v.natDegree = N ∧ W.natDegree = R ∧
      L.natDegree = N + 2 * R ∧
      P.natDegree = 12 * N - 7 * S - 1 ∧
      12 * N - 7 * S - 1 = 3 * N - 1 ∧
      ∃ m : ℕ, 0 < m ∧ N = 7 * m ∧ S = 9 * m ∧
        B.natDegree = 3 * m ∧ d.natDegree = 8 * m ∧
        v.natDegree = 7 * m ∧ W.natDegree = 5 * m ∧
        L.natDegree = 17 * m ∧ P.natDegree = 21 * m - 1 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let R := 2 * N - S
  obtain ⟨i3, kappa, v, W, T, q, hv, hvdeg, hW, hc0,
      he, hH, hBT, hqdef, hBq, hqdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_v_descent68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨i3T, vT, TT, hvT, hvTdeg, hTdef, hBTT, hTTdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨vw, Ww, hvw, hvwdeg, hWw, hWdegW, hWtop⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_W_profile68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨i3p, kappap, vp, hc0p, hsf, hroot⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_root_packet68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
    ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  rcases hpacket with
    ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hz : zeta = 0 := hrest.2.2.1
  rcases had with ⟨j4, j3, hj4, hj3, hrow0, hrow1, hrow2, hpos, hiff⟩
  rw [hz] at hrow0 hrow1
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hscale := fiveToSix_qZero_terminal_wall_scale_algebra68 N S hN hEq
  obtain ⟨m, hmpos, hNm, hSm, hD3, hV8, hR5, hL17, hP21, h3m⟩ := hscale
  have hBbound : B.natDegree ≤ D := by dsimp only [D]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hBbound hbcoeff
  have hBne : B ≠ 0 := by
    intro hzB
    apply hbcoeff
    rw [hzB, coeff_zero]
  have hdbound : d.natDegree ≤ V := by dsimp only [V]; omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hdtop
  have hddeg : d.natDegree = V :=
    natDegree_eq_of_le_of_coeff_ne_zero hdbound hdcoeff
  have hvTuniq : vT = v := by
    apply mul_left_cancel₀ hBne
    rw [← hvT, ← hv]
  subst vT
  have hi3 : i3T = i3 := by
    have hdiff : C (81 * epsilon * gamma + 27 * i3) -
        C (81 * epsilon * gamma + 27 * i3T) = B * (TT - T) := by
      linear_combination hBTT - hBT
    have hconst : C ((81 * epsilon * gamma + 27 * i3) -
        (81 * epsilon * gamma + 27 * i3T)) = B * (TT - T) := by
      rw [C_sub]
      exact hdiff
    by_contra hne
    have hsub : (81 * epsilon * gamma + 27 * i3) -
        (81 * epsilon * gamma + 27 * i3T) ≠ 0 := by
      intro hz
      have hrewrite : 81 * epsilon * gamma + 27 * i3 -
          (81 * epsilon * gamma + 27 * i3T) =
          (27 : k) * (i3 - i3T) := by ring
      rw [hrewrite] at hz
      have hi : i3 - i3T = 0 :=
        (mul_eq_zero.mp hz).resolve_left (by norm_num)
      exact hne (eq_of_sub_eq_zero hi).symm
    have hCne : (C ((81 * epsilon * gamma + 27 * i3) -
        (81 * epsilon * gamma + 27 * i3T)) : k[X]) ≠ 0 :=
      mt C_eq_zero.mp hsub
    have hQne : TT - T ≠ 0 := by
      intro hz
      apply hCne
      rw [hconst, hz, mul_zero]
    have hmul := natDegree_mul hBne hQne
    have hCdeg : (C ((81 * epsilon * gamma + 27 * i3) -
        (81 * epsilon * gamma + 27 * i3T)) : k[X]).natDegree = 0 :=
      natDegree_C _
    rw [← hconst, hCdeg, hBdeg] at hmul
    omega
  subst i3T
  have hTuniq : TT = T := by
    apply mul_left_cancel₀ hBne
    rw [← hBTT, ← hBT]
  have hvwuniq : vw = v := by
    apply mul_left_cancel₀ hBne
    rw [← hvw, ← hv]
  subst vw
  have hWdegR : W.natDegree = R := by
    have hWwW : Ww = W := by rw [hWw, hW]
    rw [← hWwW]
    dsimp only [R]
    exact hWdegW
  have hvdegN : v.natDegree = N := hvdeg
  let C0 := 81 * epsilon * gamma + 27 * i3
  let s := T - (8 : k) • (B ^ 2 * v) + (24 * gamma : k) • B
  have hsqpoly : (36 : k) • d ^ 2 - C C0 = B * s :=
    fiveToSix_qZero_terminal_square_congruence_algebra68
      gamma C0 B d v (FiveToSixQZeroFceZeroH68 B c d) T s hH hBT rfl
  let L := v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d
  have hTform : T = (2 : k) • ((3 : k) • (W * d) +
      (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B) := by
    rw [hW, ← hTuniq]
    exact hTdef
  have hWdegW : W.natDegree = 2 * N - S := hWdegR
  have hLdeg := fiveToSix_qZero_terminal_L_degree_algebra68
    gamma d v W L N S hN hS hEq hvdegN hWdegW hddeg rfl
  have hvne : v ≠ 0 := by
    intro hzv
    rw [hzv, natDegree_zero] at hvdegN
    omega
  have hWne : W ≠ 0 := by
    intro hzW
    rw [hzW, natDegree_zero] at hWdegR
    omega
  have hvtop : v.coeff N ≠ 0 := by
    have hlead : v.coeff v.natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hvne
    rwa [hvdegN] at hlead
  have hWtopR : W.coeff R ≠ 0 := by
    have hlead : W.coeff W.natDegree ≠ 0 :=
      leadingCoeff_ne_zero.mpr hWne
    rwa [hWdegR] at hlead
  have hface : ∀ x : k, B.eval x = 0 →
      (derivative B).eval x * d.eval x * L.eval x =
        -108 * terminal := by
    intro x hBx
    have hx := hroot x hBx
    rcases hx with ⟨hBpx, hdx, _, _⟩
    have hTev := fiveToSix_qZero_terminal_T_eval_algebra68
      gamma B d v W T x hBx hTform
    have hqev := fiveToSix_qZero_terminal_q_eval_algebra68
      gamma B d v W T q x hBx hqdef
    have hv'ev := fiveToSix_qZero_terminal_C0_v'_eval_algebra68
      C0 kappa B v q x hBx hBq
    have hsev := fiveToSix_qZero_terminal_s_eval_algebra68
      gamma B v T s x hBx rfl
    have hd'ev := fiveToSix_qZero_terminal_72_d_d'_eval_algebra68
      C0 B d s x hBx hsqpoly
    have hd'T : (72 : k) * d.eval x * (derivative d).eval x =
        (derivative B).eval x * T.eval x := by
      rw [hd'ev, hsev]
    have hWev : W.eval x = 4 * A.eval x + 3 * v.eval x ^ 2 := by
      have h := congrArg (fun R : k[X] => R.eval x) hW
      simpa [eval_add, eval_smul, eval_pow, smul_eq_mul] using h
    have hrow1ev := fiveToSix_qZero_terminal_rowOne_root_algebra68
      alpha gamma epsilon eta A B c d e v W x hBx hdx hv he hW hrow1
    have hLev := fiveToSix_qZero_terminal_L_eval_algebra68
      gamma d v W L x rfl
    have hr0 := fiveToSix_qZero_terminal_rowZero_root_algebra68
      alpha gamma epsilon eta terminal A B c d e v x hBx hv he hrow0
    have hC0eval : (36 : k) * d.eval x ^ 2 = C0 := by
      have hev := congrArg (fun R : k[X] => R.eval x) hsqpoly
      simp only [eval_sub, eval_smul, eval_mul, eval_pow, eval_C,
        smul_eq_mul] at hev
      rw [hBx] at hev
      simp only [zero_mul, sub_zero] at hev
      linear_combination hev
    have hslopeC0 : C0 * ((derivative A).eval x * v.eval x -
        2 * (derivative B).eval x) = 162 * terminal := by
      linear_combination (162 : k) * hr0 +
        ((derivative A).eval x * v.eval x -
          2 * (derivative B).eval x) * hC0eval.symm
    have hbridge := fiveToSix_qZero_terminal_divisor_bridge_algebra68
      gamma terminal C0 A d v W T q x ((derivative B).eval x)
      hdx hWev hC0eval hv'ev hd'T hqev hTev hslopeC0 hrow1ev
    rw [hLev]
    exact hbridge
  let v0 := (4 * kappa) / C0
  let c1 := (162 : k) * terminal / C0
  let delta := C0 / 36
  have hkappa : kappa ≠ 0 := by
    intro hk0
    have hconst : ∀ x : k, B.eval x = 0 →
        (derivative B).eval x =
          -108 * terminal / (48 * delta) := by
      intro x hBx
      have hx := hroot x hBx
      rcases hx with ⟨_, hdx, _, _⟩
      have hvx : v.eval x = 0 := by
        have hv0 := fiveToSix_qZero_terminal_v0_eval_algebra68
          C0 kappa B v q x hc0 hBx hBq
        rw [hk0] at hv0
        simpa using hv0
      have hLev := fiveToSix_qZero_terminal_kappa_zero_L_eval_algebra68
        gamma d v W L x hvx rfl
      have hdelta0 : delta ≠ 0 := by
        dsimp only [delta]
        exact div_ne_zero hc0 (by norm_num)
      have hsqd : d.eval x ^ 2 = delta :=
        fiveToSix_qZero_terminal_delta_eval_algebra68
          C0 B d s x hBx hsqpoly
      exact fiveToSix_qZero_terminal_kappa_zero_derivative_eval_algebra68
        terminal delta d L x ((derivative B).eval x)
        hdelta0 hsqd hLev (hface x hBx)
    have hdegB : 3 ≤ B.natDegree := by
      rw [hBdeg]
      dsimp only [D]
      omega
    exact fiveToSix_qZero_terminal_constant_on_simple_roots_impossible_algebra68
      (-108 * terminal / (48 * delta)) hBne hsf hdegB hconst
  have hrootids : ∀ x : k, B.eval x = 0 →
      v.eval x = v0 ∧
        d.eval x ^ 2 = delta ∧
        (derivative B).eval x * L.eval x +
          24 * c1 * d.eval x = 0 ∧
        C0 * (derivative W).eval x +
          6 * (derivative B).eval x * d.eval x *
            (W.eval x ^ 2 + 6 * v0 ^ 2 * W.eval x - 72 * gamma) =
          0 := by
    intro x hBx
    have hx := hroot x hBx
    rcases hx with ⟨hBpx, hdx, _, _⟩
    have hvx : v.eval x = v0 :=
      fiveToSix_qZero_terminal_v0_eval_algebra68
        C0 kappa B v q x hc0 hBx hBq
    have hsqd : d.eval x ^ 2 = delta :=
      fiveToSix_qZero_terminal_delta_eval_algebra68
        C0 B d s x hBx hsqpoly
    have hC0eval : (36 : k) * d.eval x ^ 2 = C0 := by
      have hev := congrArg (fun R : k[X] => R.eval x) hsqpoly
      simp only [eval_sub, eval_smul, eval_mul, eval_pow, eval_C,
        smul_eq_mul] at hev
      rw [hBx] at hev
      simp only [zero_mul, sub_zero] at hev
      linear_combination hev
    have hcleared := fiveToSix_qZero_terminal_cleared_bridge_eval_algebra68
      terminal C0 c1 delta d L x ((derivative B).eval x)
      hdx hc0 rfl rfl hsqd (hface x hBx)
    have hTev := fiveToSix_qZero_terminal_T_eval_algebra68
      gamma B d v W T x hBx hTform
    have hqev := fiveToSix_qZero_terminal_q_eval_algebra68
      gamma B d v W T q x hBx hqdef
    have hv'raw := fiveToSix_qZero_terminal_C0_v'_eval_algebra68
      C0 kappa B v q x hBx hBq
    have hsev := fiveToSix_qZero_terminal_s_eval_algebra68
      gamma B v T s x hBx rfl
    have hd'raw := fiveToSix_qZero_terminal_72_d_d'_eval_algebra68
      C0 B d s x hBx hsqpoly
    have hv'ev := fiveToSix_qZero_terminal_v'_congruence_eval_algebra68
      C0 v0 d v W T q x ((derivative B).eval x)
      hvx hv'raw hqev hTev
    have hd'ev := fiveToSix_qZero_terminal_d'_congruence_eval_algebra68
      d W T s x ((derivative B).eval x) hdx hd'raw hsev hTev
    have hWev : W.eval x = 4 * A.eval x + 3 * v.eval x ^ 2 := by
      have h := congrArg (fun R : k[X] => R.eval x) hW
      simpa [eval_add, eval_smul, eval_pow, smul_eq_mul] using h
    have hW'ev := fiveToSix_qZero_terminal_W'_eval_algebra68 A v W x hW
    have hrow1ev := fiveToSix_qZero_terminal_rowOne_root_algebra68
      alpha gamma epsilon eta A B c d e v W x hBx hdx hv he hW hrow1
    have hode := fiveToSix_qZero_terminal_ode_eval_algebra68
      gamma C0 v0 A d v W x ((derivative B).eval x)
      hdx hWev hW'ev hvx hC0eval hv'ev hd'ev hrow1ev
    exact ⟨hvx, hsqd, hcleared, hode⟩
  have hclearedP : B ∣ derivative B * L + C (24 * c1) * d := by
    refine fiveToSix_qZero_terminal_squarefree_dvd_of_eval_eq_zero_algebra68
      hBne hsf ?_
    intro x hBx
    have hx := (hrootids x hBx).2.2.1
    simp only [eval_add, eval_mul, eval_C]
    linear_combination hx
  let Q := W ^ 2 + C (6 * v0 ^ 2) * W - C (72 * gamma)
  let P := C0 • derivative W +
    (6 : k) • (derivative B * d * Q)
  have hodeP : B ∣ P := by
    refine fiveToSix_qZero_terminal_squarefree_dvd_of_eval_eq_zero_algebra68
      hBne hsf ?_
    intro x hBx
    have hx := (hrootids x hBx).2.2.2
    have hQev : Q.eval x =
        W.eval x ^ 2 + 6 * v0 ^ 2 * W.eval x - 72 * gamma := by
      dsimp only [Q]
      simp [eval_add, eval_sub, eval_mul, eval_pow, eval_C]
    dsimp only [P]
    simp only [eval_add, eval_smul, eval_mul, smul_eq_mul]
    rw [hQev]
    linear_combination hx
  have hodeg := fiveToSix_qZero_terminal_ode_degree_algebra68
    gamma v0 C0 B d W N S hN hS hEq hBdeg hddeg hWdegW hbcoeff hdcoeff
    hWtopR hc0
  have hPdeg : P.natDegree = 12 * N - 7 * S - 1 := hodeg.2.2.1
  have hwallP : 12 * N - 7 * S - 1 = 3 * N - 1 := hodeg.2.2.2.2
  have hmdata : ∃ m : ℕ, 0 < m ∧ N = 7 * m ∧ S = 9 * m ∧
      B.natDegree = 3 * m ∧ d.natDegree = 8 * m ∧
      v.natDegree = 7 * m ∧ W.natDegree = 5 * m ∧
      L.natDegree = 17 * m ∧ P.natDegree = 21 * m - 1 := by
    refine ⟨m, hmpos, hNm, hSm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hBdeg' : B.natDegree = 3 * N - 2 * S := hBdeg
      rw [hBdeg', hD3]
    · have hddeg' : d.natDegree = 5 * N - 3 * S := hddeg
      rw [hddeg', hV8]
    · rw [hvdegN, hNm]
    · have hWdeg' : W.natDegree = 2 * N - S := hWdegR
      rw [hWdeg', hR5]
    · have hLdeg' : L.natDegree = N + 2 * (2 * N - S) := hLdeg.1
      rw [hLdeg', hL17]
    · rw [hPdeg, hP21]
  refine ⟨i3, kappa, v, W, T, q, L, hc0, hkappa, hW, rfl, hBq, hsf,
    hrootids, hclearedP, hodeP, hvdegN, hWdegR, hLdeg.1, hPdeg, hwallP,
    hmdata⟩

#print axioms fiveToSix_qZero_terminal_wall_scale_algebra68
#print axioms fiveToSix_qZero_terminal_v0_eval_algebra68
#print axioms fiveToSix_qZero_terminal_delta_eval_algebra68
#print axioms fiveToSix_qZero_terminal_c1_delta_mul_algebra68
#print axioms fiveToSix_qZero_terminal_cleared_bridge_eval_algebra68
#print axioms fiveToSix_qZero_terminal_v'_congruence_eval_algebra68
#print axioms fiveToSix_qZero_terminal_d'_congruence_eval_algebra68
#print axioms fiveToSix_qZero_terminal_W_derivative_algebra68
#print axioms fiveToSix_qZero_terminal_W'_eval_algebra68
#print axioms fiveToSix_qZero_terminal_ode_eval_algebra68
#print axioms fiveToSix_qZero_terminal_ode_Q_degree_algebra68
#print axioms fiveToSix_qZero_terminal_ode_degree_algebra68
#print axioms fiveToSix_qZero_terminal_kappa_zero_L_eval_algebra68
#print axioms fiveToSix_qZero_terminal_kappa_zero_derivative_eval_algebra68
#print axioms fiveToSix_qZero_terminal_squarefree_roots_nodup_algebra68
#print axioms fiveToSix_qZero_terminal_constant_on_simple_roots_impossible_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_root_count_closure68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootCountClosure68

end Max11DegreeRoutes
