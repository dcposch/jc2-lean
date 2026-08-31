import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalRootRowOneScratch

/-! # Terminal simple-root divisor bridge

At every simple root of `B`, the landed quotient identities
`C0 v' = B' q`, `72 d d' = B' T`, `q = -v T`, and `T = 6 W d` combine
with the pinned row-one packet and the row-zero slope to give the exact
scalar face
`B' d (v (W² - 72 γ) + 48 d) = -108 terminal`.
Squarefreeness of `B` then lifts the face to the polynomial divisor
`B ∣ B' d L + C (108 terminal)` for
`L = v (W² - C (72 γ)) + 48 d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalDivisorBridge68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Explicit `T` evaluates to `6 W d` on the zero set of `B`. -/
theorem fiveToSix_qZero_terminal_T_eval_algebra68
    (gamma : k) (B d v W T : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hT : T = (2 : k) • ((3 : k) • (W * d) +
      (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B)) :
    T.eval x = 6 * W.eval x * d.eval x := by
  have hT0 := congrArg (fun R : k[X] => R.eval x) hT
  simp only [eval_add, eval_sub, eval_smul, eval_mul, eval_pow,
    smul_eq_mul] at hT0
  rw [hBx] at hT0
  norm_num at hT0
  linear_combination hT0

/-- The complementary quotient `q` evaluates to `-v T` on the zero set
of `B`. -/
theorem fiveToSix_qZero_terminal_q_eval_algebra68
    (gamma : k) (B d v W T q : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hq : q = (2 / 3 : k) • (B ^ 2 * W - (24 : k) • (B * d) -
      (9 * gamma : k) • (B * v)) - v * T) :
    q.eval x = -v.eval x * T.eval x := by
  have hq0 := congrArg (fun R : k[X] => R.eval x) hq
  simp only [eval_add, eval_sub, eval_smul, eval_mul, eval_pow,
    smul_eq_mul] at hq0
  rw [hBx] at hq0
  norm_num at hq0
  linear_combination hq0

/-- Differentiating `C0 v - C (4 κ) = B q` yields `C0 v' = B' q` on the
zero set of `B`. -/
theorem fiveToSix_qZero_terminal_C0_v'_eval_algebra68
    (C0 kappa : k) (B v q : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hBq : (C0 : k) • v - C (4 * kappa) = B * q) :
    C0 * (derivative v).eval x =
      (derivative B).eval x * q.eval x := by
  have h := congrArg (fun R : k[X] => (derivative R).eval x) hBq
  simp only [derivative_sub, derivative_smul, derivative_C, derivative_mul,
    eval_add, eval_sub, eval_smul, eval_mul, eval_zero] at h
  rw [hBx] at h
  simpa only [smul_eq_mul, sub_zero, zero_mul, add_zero] using h

/-- The compensated square fiber agrees with `T` on the zero set of `B`. -/
theorem fiveToSix_qZero_terminal_s_eval_algebra68
    (gamma : k) (B v T s : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hs : s = T - (8 : k) • (B ^ 2 * v) + (24 * gamma : k) • B) :
    s.eval x = T.eval x := by
  have h := congrArg (fun R : k[X] => R.eval x) hs
  simp only [eval_add, eval_sub, eval_smul, eval_mul, eval_pow] at h
  rw [hBx] at h
  norm_num at h
  linear_combination h

/-- Differentiating `36 d² - C C0 = B s` yields `72 d d' = B' s` on the
zero set of `B`. -/
theorem fiveToSix_qZero_terminal_72_d_d'_eval_algebra68
    (C0 : k) (B d s : k[X]) (x : k)
    (hBx : B.eval x = 0)
    (hsq : (36 : k) • d ^ 2 - C C0 = B * s) :
    (72 : k) * d.eval x * (derivative d).eval x =
      (derivative B).eval x * s.eval x := by
  have h := congrArg (fun R : k[X] => (derivative R).eval x) hsq
  simp only [derivative_sub, derivative_smul, derivative_C, derivative_mul,
    derivative_pow, eval_add, eval_sub, eval_smul, eval_mul, eval_pow,
    eval_zero, eval_C, smul_eq_mul, sub_zero, zero_mul, add_zero, one_mul,
    pow_one] at h
  rw [hBx] at h
  norm_num at h
  linear_combination h

/-- The `H`-fiber identity rearranges to the exact square congruence
`36 d² - C C0 = B s`. -/
theorem fiveToSix_qZero_terminal_square_congruence_algebra68
    (gamma C0 : k) (B d v H T s : k[X])
    (hH : H = (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
      (9 : k) • d ^ 2)
    (hBT : (4 : k) • H - C C0 = B * T)
    (hs : s = T - (8 : k) • (B ^ 2 * v) + (24 * gamma : k) • B) :
    (36 : k) • d ^ 2 - C C0 = B * s := by
  calc
    (36 : k) • d ^ 2 - C C0 =
        ((4 : k) • H - C C0) - (8 : k) • (B ^ 3 * v) +
          (24 * gamma : k) • B ^ 2 := by
      rw [hH]
      module
    _ = B * T - (8 : k) • (B ^ 3 * v) +
        (24 * gamma : k) • B ^ 2 := by rw [hBT]
    _ = B * s := by
      rw [hs]
      simp only [mul_add, mul_sub, mul_smul_comm, pow_succ]
      ring

/-- Evaluation of the bridge polynomial `L`. -/
theorem fiveToSix_qZero_terminal_L_eval_algebra68
    (gamma : k) (d v W L : k[X]) (x : k)
    (hL : L = v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d) :
    L.eval x =
      v.eval x * (W.eval x ^ 2 - 72 * gamma) + 48 * d.eval x := by
  rw [hL]
  simp [eval_add, eval_sub, eval_mul, eval_pow, eval_smul, eval_C,
    smul_eq_mul]

/-- Combining the four root identities with the pinned row-one packet
and the row-zero slope produces the exact scalar face. -/
theorem fiveToSix_qZero_terminal_divisor_bridge_algebra68
    (gamma terminal C0 : k) (A d v W T q : k[X]) (x : k)
    (Bp : k)
    (hdx : d.eval x ≠ 0)
    (hW : W.eval x = 4 * A.eval x + 3 * v.eval x ^ 2)
    (hsq : (36 : k) * d.eval x ^ 2 = C0)
    (hv' : C0 * (derivative v).eval x = Bp * q.eval x)
    (hd' : (72 : k) * d.eval x * (derivative d).eval x = Bp * T.eval x)
    (hq : q.eval x = -v.eval x * T.eval x)
    (hT : T.eval x = 6 * W.eval x * d.eval x)
    (hslope : C0 * ((derivative A).eval x * v.eval x - 2 * Bp) =
      162 * terminal)
    (hrow : Bp * (A.eval x * W.eval x - 18 * gamma) +
      6 * (derivative A).eval x * d.eval x -
      9 * d.eval x * v.eval x * (derivative v).eval x -
      9 * (derivative d).eval x * v.eval x ^ 2 = 0) :
    Bp * d.eval x *
      (v.eval x * (W.eval x ^ 2 - 72 * gamma) + 48 * d.eval x) =
      -108 * terminal := by
  have hvT : C0 * (derivative v).eval x +
      Bp * v.eval x * T.eval x = 0 := by
    linear_combination hv' + Bp * hq
  have hvW : C0 * (derivative v).eval x +
      6 * Bp * v.eval x * W.eval x * d.eval x = 0 := by
    rw [hT] at hvT
    linear_combination hvT
  have hdW : 72 * d.eval x * (derivative d).eval x -
      6 * Bp * W.eval x * d.eval x = 0 := by
    rw [hT] at hd'
    linear_combination hd'
  have hd12 : 12 * (derivative d).eval x - Bp * W.eval x = 0 := by
    have hprod : d.eval x *
        (72 * (derivative d).eval x - 6 * Bp * W.eval x) = 0 := by
      linear_combination hdW
    have h72 : 72 * (derivative d).eval x - 6 * Bp * W.eval x = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hdx
    linear_combination (1 / 6 : k) * h72
  have hv6 : 6 * d.eval x * (derivative v).eval x +
      Bp * v.eval x * W.eval x = 0 := by
    have hcancel : 36 * d.eval x ^ 2 * (derivative v).eval x +
        6 * Bp * v.eval x * W.eval x * d.eval x = 0 := by
      linear_combination hvW + (derivative v).eval x * hsq
    have hprod : 6 * d.eval x *
        (6 * d.eval x * (derivative v).eval x +
          Bp * v.eval x * W.eval x) = 0 := by
      linear_combination hcancel
    exact (mul_eq_zero.mp hprod).resolve_left
      (mul_ne_zero (by norm_num) hdx)
  have hrowW : Bp * (A.eval x * W.eval x - 18 * gamma) +
      6 * (derivative A).eval x * d.eval x +
      (3 / 4 : k) * Bp * v.eval x ^ 2 * W.eval x = 0 := by
    linear_combination hrow + (3 / 2 : k) * v.eval x * hv6 +
      (3 / 4 : k) * v.eval x ^ 2 * hd12
  have hrow4 : 4 * Bp * (A.eval x * W.eval x - 18 * gamma) +
      24 * (derivative A).eval x * d.eval x +
      3 * Bp * v.eval x ^ 2 * W.eval x = 0 := by
    linear_combination (4 : k) * hrowW
  have hrowA : Bp * (W.eval x ^ 2 - 72 * gamma) +
      24 * (derivative A).eval x * d.eval x = 0 := by
    linear_combination hrow4 + (Bp * W.eval x) * hW
  have hslope36 : 36 * d.eval x ^ 2 *
      ((derivative A).eval x * v.eval x - 2 * Bp) -
      162 * terminal = 0 := by
    linear_combination hslope +
      ((derivative A).eval x * v.eval x - 2 * Bp) * hsq
  have hslope2 : 2 * d.eval x ^ 2 *
      ((derivative A).eval x * v.eval x - 2 * Bp) -
      9 * terminal = 0 := by
    linear_combination (1 / 18 : k) * hslope36
  have hrowAv : Bp * d.eval x * v.eval x *
      (W.eval x ^ 2 - 72 * gamma) +
      24 * (derivative A).eval x * d.eval x ^ 2 * v.eval x = 0 := by
    linear_combination (d.eval x * v.eval x) * hrowA
  linear_combination hrowAv - 12 * hslope2

/-- Squarefreeness of `B` promotes vanishing on the zero set of `B` to
polynomial divisibility. -/
theorem fiveToSix_qZero_terminal_squarefree_dvd_of_eval_eq_zero_algebra68
    {B P : k[X]} (hB : B ≠ 0)
    (hsf : IsCoprime B (derivative B))
    (hroot : ∀ x : k, B.eval x = 0 → P.eval x = 0) :
    B ∣ P := by
  classical
  have hsimple : ∀ a : k, B.eval a = 0 →
      (derivative B).eval a ≠ 0 := by
    intro a ha
    have hx :=
      (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
        (k := k) k B (derivative B)).mp hsf a
    rw [aeval_def, aeval_def] at hx
    exact hx.resolve_left (not_ne_iff.mpr ha)
  by_cases hP0 : P = 0
  · simp [hP0]
  · refine (IsAlgClosed.splits B).dvd_of_roots_le_roots hB ?_
    refine Multiset.le_iff_count.mpr fun a => ?_
    simp only [count_roots]
    by_cases ha : B.eval a = 0
    · have hpos : 0 < B.rootMultiplicity a :=
        (rootMultiplicity_pos hB).mpr ha
      have hnot : ¬ 1 < B.rootMultiplicity a := by
        intro hlt
        have hboth := (one_lt_rootMultiplicity_iff_isRoot hB).mp hlt
        exact hsimple a ha (IsRoot.eq_zero hboth.2)
      have h1 : B.rootMultiplicity a = 1 := by omega
      have hge : 1 ≤ P.rootMultiplicity a :=
        (rootMultiplicity_pos hP0).mpr (hroot a ha)
      simp [h1, hge]
    · have hz : B.rootMultiplicity a = 0 :=
        rootMultiplicity_eq_zero ha
      simp [hz]

/-- Exact degree and top coefficient of
`L = v (W² - C (72 γ)) + 48 d` on the `9N = 7S` wall. -/
theorem fiveToSix_qZero_terminal_L_degree_algebra68
    (gamma : k) (d v W L : k[X]) (N S : ℕ)
    (hN : 0 < N) (hS : 0 < S) (hEq : 9 * N = 7 * S)
    (hvdeg : v.natDegree = N)
    (hWdeg : W.natDegree = 2 * N - S)
    (hddeg : d.natDegree = 5 * N - 3 * S)
    (hL : L = v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d) :
    let R := 2 * N - S
    L.natDegree = N + 2 * R ∧
      L.coeff (N + 2 * R) = v.coeff N * W.coeff R ^ 2 := by
  let R := 2 * N - S
  change L.natDegree = N + 2 * R ∧
    L.coeff (N + 2 * R) = v.coeff N * W.coeff R ^ 2
  have hRpos : 0 < R := by dsimp only [R]; omega
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hvdeg
    omega
  have hWne : W ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hWdeg
    omega
  have hW2deg : (W ^ 2).natDegree = 2 * R := by
    rw [natDegree_pow, hWdeg]
  have hW2ne : W ^ 2 ≠ 0 := pow_ne_zero 2 hWne
  have hClt : (C (72 * gamma) : k[X]).natDegree < (W ^ 2).natDegree := by
    rw [hW2deg]
    compute_degree
    omega
  have hW2Cdeg : (W ^ 2 - C (72 * gamma)).natDegree = 2 * R := by
    rw [natDegree_sub_eq_left_of_natDegree_lt hClt, hW2deg]
  have hW2Cne : W ^ 2 - C (72 * gamma) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hW2Cdeg
    omega
  have hproddeg : (v * (W ^ 2 - C (72 * gamma))).natDegree =
      N + 2 * R := by
    rw [natDegree_mul hvne hW2Cne, hvdeg, hW2Cdeg]
  have hprodne : v * (W ^ 2 - C (72 * gamma)) ≠ 0 :=
    mul_ne_zero hvne hW2Cne
  have hdle : ((48 : k) • d).natDegree ≤ 5 * N - 3 * S := by
    compute_degree
    omega
  have hlow : ((48 : k) • d).natDegree < N + 2 * R := by
    have : 5 * N - 3 * S < N + 2 * R := by
      dsimp only [R]
      omega
    exact lt_of_le_of_lt hdle this
  have hLdecomp : L = v * (W ^ 2 - C (72 * gamma)) +
      (48 : k) • d := hL
  have hlow' : ((48 : k) • d).natDegree <
      (v * (W ^ 2 - C (72 * gamma))).natDegree := by
    rwa [hproddeg]
  have hLdeg : L.natDegree = N + 2 * R := by
    rw [hLdecomp, natDegree_add_eq_left_of_natDegree_lt hlow', hproddeg]
  have hW2coeff : (W ^ 2).coeff (2 * R) = W.coeff R ^ 2 := by
    have h := coeff_pow_at_bound68 W R 2 hWdeg.le
    simpa only [pow_two, Nat.mul_comm] using h
  have hCcoeff : (C (72 * gamma) : k[X]).coeff (2 * R) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_eq hClt hW2deg)
  have hW2Ccoeff : (W ^ 2 - C (72 * gamma)).coeff (2 * R) =
      W.coeff R ^ 2 := by
    rw [coeff_sub, hW2coeff, hCcoeff, sub_zero]
  have hprodcoeff : (v * (W ^ 2 - C (72 * gamma))).coeff (N + 2 * R) =
      v.coeff N * W.coeff R ^ 2 := by
    have h := coeff_mul_at_bounds68 v (W ^ 2 - C (72 * gamma)) N (2 * R)
      hvdeg.le hW2Cdeg.le
    rw [hW2Ccoeff] at h
    exact h
  have h48coeff : ((48 : k) • d).coeff (N + 2 * R) = 0 :=
    coeff_eq_zero_of_natDegree_lt hlow
  have hLcoeff : L.coeff (N + 2 * R) = v.coeff N * W.coeff R ^ 2 := by
    rw [hLdecomp, coeff_add, hprodcoeff, h48coeff, add_zero]
  exact ⟨hLdeg, hLcoeff⟩

/-- Exact degree and top coefficient of `B' d L` on the `9N = 7S`
wall. -/
theorem fiveToSix_qZero_terminal_BdL_degree_algebra68
    (B d L : k[X]) (N S : ℕ)
    (hN : 0 < N) (hS : 0 < S) (hEq : 9 * N = 7 * S)
    (hBdeg : B.natDegree = 3 * N - 2 * S)
    (hddeg : d.natDegree = 5 * N - 3 * S)
    (hLdeg : L.natDegree = 5 * N - 2 * S)
    (hBtop : B.coeff (3 * N - 2 * S) ≠ 0)
    (hdtop : d.coeff (5 * N - 3 * S) ≠ 0)
    (hLtop : L.coeff (5 * N - 2 * S) ≠ 0) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    (derivative B).natDegree = D - 1 ∧
      (derivative B * d * L).natDegree = 13 * N - 7 * S - 1 ∧
      (derivative B * d * L).coeff (13 * N - 7 * S - 1) =
        B.coeff D * (D : k) * d.coeff V * L.coeff (5 * N - 2 * S) ∧
      13 * N - 7 * S - 1 = 4 * N - 1 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  change (derivative B).natDegree = D - 1 ∧
    (derivative B * d * L).natDegree = 13 * N - 7 * S - 1 ∧
    (derivative B * d * L).coeff (13 * N - 7 * S - 1) =
      B.coeff D * (D : k) * d.coeff V * L.coeff (5 * N - 2 * S) ∧
    13 * N - 7 * S - 1 = 4 * N - 1
  have hDpos : 0 < D := by dsimp only [D]; omega
  have hwall : 13 * N - 7 * S - 1 = 4 * N - 1 := by omega
  have hidx : D - 1 + V + (5 * N - 2 * S) = 13 * N - 7 * S - 1 := by
    dsimp only [D, V]
    omega
  have hB'le : (derivative B).natDegree ≤ D - 1 :=
    (natDegree_derivative_le B).trans (by rw [hBdeg])
  have hB'coeff : (derivative B).coeff (D - 1) = B.coeff D * (D : k) :=
    coeff_derivative_at_bound68 B D hDpos
  have hDcast : (D : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt hDpos)
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
  have hLne : L ≠ 0 := by
    intro hz
    apply hLtop
    rw [hz, coeff_zero]
  have hBdne : derivative B * d ≠ 0 := mul_ne_zero hB'ne hdne
  have hBddeg : (derivative B * d).natDegree = D - 1 + V := by
    rw [natDegree_mul hB'ne hdne, hB'deg, hddeg]
  have hBdLdeg : (derivative B * d * L).natDegree =
      13 * N - 7 * S - 1 := by
    rw [natDegree_mul hBdne hLne, hBddeg, hLdeg, hidx]
  have hBdcoeff : (derivative B * d).coeff (D - 1 + V) =
      B.coeff D * (D : k) * d.coeff V := by
    have h := coeff_mul_at_bounds68 (derivative B) d (D - 1) V
      hB'deg.le hddeg.le
    rw [hB'coeff] at h
    simpa only [mul_assoc] using h
  have hBdLle : (derivative B * d).natDegree ≤ D - 1 + V := hBddeg.le
  have hBdLcoeff : (derivative B * d * L).coeff (13 * N - 7 * S - 1) =
      B.coeff D * (D : k) * d.coeff V * L.coeff (5 * N - 2 * S) := by
    have h := coeff_mul_at_bounds68 (derivative B * d) L (D - 1 + V)
      (5 * N - 2 * S) hBdLle hLdeg.le
    rw [show D - 1 + V + (5 * N - 2 * S) = 13 * N - 7 * S - 1
      from hidx] at h
    rw [hBdcoeff] at h
    simpa only [mul_assoc] using h
  exact ⟨hB'deg, hBdLdeg, hBdLcoeff, hwall⟩

/-- Source-facing assembly: every simple terminal root obeys the exact
scalar face, the polynomial `B` divides `B' d L + C (108 terminal)`,
and `B' d L` has the recorded degree and top coefficient. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_divisor_bridge68
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
      81 * epsilon * gamma + 27 * i3 ≠ 0 ∧
      W = (4 : k) • A + (3 : k) • v ^ 2 ∧
      L = v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d ∧
      IsCoprime B (derivative B) ∧
      (∀ x : k, B.eval x = 0 →
        (derivative B).eval x * d.eval x * L.eval x =
          -108 * terminal) ∧
      B ∣ derivative B * d * L + C (108 * terminal) ∧
      v.natDegree = N ∧ W.natDegree = R ∧
      L.natDegree = N + 2 * R ∧
      L.coeff (N + 2 * R) = v.coeff N * W.coeff R ^ 2 ∧
      (derivative B).natDegree = D - 1 ∧
      (derivative B * d * L).natDegree = 13 * N - 7 * S - 1 ∧
      (derivative B * d * L).coeff (13 * N - 7 * S - 1) =
        B.coeff D * (D : k) * d.coeff V *
          (v.coeff N * W.coeff R ^ 2) ∧
      13 * N - 7 * S - 1 = 4 * N - 1 := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let R := 2 * N - S
  change ∃ i3 kappa : k, ∃ v W T q L : k[X],
    81 * epsilon * gamma + 27 * i3 ≠ 0 ∧
    W = (4 : k) • A + (3 : k) • v ^ 2 ∧
    L = v * (W ^ 2 - C (72 * gamma)) + (48 : k) • d ∧
    IsCoprime B (derivative B) ∧
    (∀ x : k, B.eval x = 0 →
      (derivative B).eval x * d.eval x * L.eval x =
        -108 * terminal) ∧
    B ∣ derivative B * d * L + C (108 * terminal) ∧
    v.natDegree = N ∧ W.natDegree = R ∧
    L.natDegree = N + 2 * R ∧
    L.coeff (N + 2 * R) = v.coeff N * W.coeff R ^ 2 ∧
    (derivative B).natDegree = D - 1 ∧
    (derivative B * d * L).natDegree = 13 * N - 7 * S - 1 ∧
    (derivative B * d * L).coeff (13 * N - 7 * S - 1) =
      B.coeff D * (D : k) * d.coeff V *
        (v.coeff N * W.coeff R ^ 2) ∧
    13 * N - 7 * S - 1 = 4 * N - 1
  obtain ⟨i3, kappa, v, W, T, q, hv, hvdeg, hW, hc0,
      he, hH, hBT, hqdef, hBq, hqdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_v_descent68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨i3T, vT, TT, hvT, hvTdeg, hTdef, hBTT, hTTdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨vw, Ww, hvw, hvwdeg, hWw, hWdeg, hWtop⟩ :=
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
  have hDpos : 0 < D := by dsimp only [D]; omega
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
  have hWdegW : W.natDegree = 2 * N - S := by
    have hWwW : Ww = W := by rw [hWw, hW]
    rw [← hWwW]
    exact hWdeg
  have hvdegN : v.natDegree = N := hvdeg
  have hWdegR : W.natDegree = R := by
    dsimp only [R]
    exact hWdegW
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
  have hLtop : L.coeff (N + 2 * R) ≠ 0 := by
    rw [hLdeg.2]
    exact mul_ne_zero hvtop (pow_ne_zero 2 hWtopR)
  have hLdeg' : L.natDegree = 5 * N - 2 * S := by
    have : N + 2 * R = 5 * N - 2 * S := by dsimp only [R]; omega
    rw [← this]
    exact hLdeg.1
  have hLtop' : L.coeff (5 * N - 2 * S) ≠ 0 := by
    have : N + 2 * R = 5 * N - 2 * S := by dsimp only [R]; omega
    rwa [← this]
  have hBdL := fiveToSix_qZero_terminal_BdL_degree_algebra68
    B d L N S hN hS hEq hBdeg hddeg hLdeg' hbcoeff hdcoeff hLtop'
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
  have hP : B ∣ derivative B * d * L + C (108 * terminal) := by
    refine fiveToSix_qZero_terminal_squarefree_dvd_of_eval_eq_zero_algebra68
      hBne hsf ?_
    intro x hBx
    have hfacex := hface x hBx
    simp only [eval_add, eval_mul, eval_C]
    linear_combination hfacex
  refine ⟨i3, kappa, v, W, T, q, L, hc0, hW, rfl, hsf, hface, hP,
    hvdegN, hWdegR, hLdeg.1, hLdeg.2, hBdL.1, hBdL.2.1, ?_, hBdL.2.2.2⟩
  have : L.coeff (5 * N - 2 * S) = v.coeff N * W.coeff R ^ 2 := by
    have hidx : N + 2 * R = 5 * N - 2 * S := by dsimp only [R]; omega
    rw [← hidx, hLdeg.2]
  rw [hBdL.2.2.1, this]

#print axioms fiveToSix_qZero_terminal_T_eval_algebra68
#print axioms fiveToSix_qZero_terminal_q_eval_algebra68
#print axioms fiveToSix_qZero_terminal_C0_v'_eval_algebra68
#print axioms fiveToSix_qZero_terminal_s_eval_algebra68
#print axioms fiveToSix_qZero_terminal_72_d_d'_eval_algebra68
#print axioms fiveToSix_qZero_terminal_square_congruence_algebra68
#print axioms fiveToSix_qZero_terminal_L_eval_algebra68
#print axioms fiveToSix_qZero_terminal_divisor_bridge_algebra68
#print axioms fiveToSix_qZero_terminal_squarefree_dvd_of_eval_eq_zero_algebra68
#print axioms fiveToSix_qZero_terminal_L_degree_algebra68
#print axioms fiveToSix_qZero_terminal_BdL_degree_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_divisor_bridge68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalDivisorBridge68

end Max11DegreeRoutes
