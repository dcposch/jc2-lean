import Grok68VanishingAInductionStepScratch

/-! # Charged `Δ`/`H` profiles on the `q=0` vanishing-A remainders

After vanishing of `A` through `k=D` and matching through `D`, the
comparison polynomials
`c_Cc X^N B - B_D c` and `B_D e + c_Cc X^N d` have degree at most
`N-1` and `E-D-1`.  Those bounds are not the identities `r_c=r_e=0`
that `vanishingA_zero_remainder_impossible68` needs.

The wall already supplies exact `Rce=(3/4)γ B^2+(9/8)C(i_3)` and
`Fce=C(Fce_0)`.  Syzygy (S1) therefore writes the discriminant
descent as `72 Fce_0 (c+C(3γ/2))` rather than `0`.  The `Fce_0`
term has degree `Cc`, strictly below the Rest top `3D+Cc`, so the
same degree comparison as on the zero-`Fce` branch still gives
`deg Δ = 3D+Cc-V` with top `3 B_D d_V`.  Syzygy (S2) then drops
`H=4B^2 c+9d^2` to degree `N`; the extra `-3 d Fce_0` has degree
`V`, below the `c H` top `D+p`.

Those profiles do **not** force `r_c=r_e=0`.  Against the committed
weights `deg B=D`, `deg d=V`, `deg(B^3)=3D`:

* `deg(B^2 r_c) ≤ 2D+(N-1)` still reaches above `N`, so `deg H≤N`
  determines high remainder coefficients rather than killing them;
* `B R_e - d R_c = B_D (1/9 B^3 - (3/2)γ d - (3/4)ε B + C(Fce_0))`
  has right-hand degree `3D`, while each left-hand factor is allowed
  up to `E-1`, so the identity is consistent with a nonzero remainder.

CAS (`scripts/max11_cas_run.py`, `vanishing-a-remainder-closure`) on
the charts `m=2,3` (i.e. `(N,S)=(14,18)` and `(21,27)`): the monomial
slice `B=X^D` of the `H`+I4 system leaves `r_c` in degrees `0..m` and
`r_e` in degrees `5m..6m`, but with `Fce_0=0` (off this chamber).  On
`Fce_0≠0` samples at `m=1`, `H`+I4 occupies all remainder degrees
`0..N-1` and `0..E-D-1`.  The `N-1` / `E-D-1` bounds are therefore
not improved to the zero polynomial.

This is not a closure.  Named residual: comparison remainders of
degree at most `N-1` and `E-D-1`, together with `deg Δ = 3D+Cc-V`
(top `3 B_D d_V`) and `deg H ≤ N`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingARemainderClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Comparison identity -/

/-- The two comparison polynomials reconstruct `Be+cd` after multiplying
by the leading coefficient of `B`. -/
theorem fiveToSix_qZero_comparison_Be_cd_algebra68
    (B c d e : k[X]) (N D Cc : ℕ) :
    B * (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d) -
        d * (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c) =
      C (B.coeff D) * (B * e + c * d) := by
  ring

/-! ## Charged discriminant descent -/

/-- On this chamber `Rce` is exact and `Fce` is constant, so (S1) writes
the discriminant descent as a multiple of `c+C(3γ/2)`, not as zero. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_descent68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
    let Rce := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2 + (9 / 2 * gamma : k) • e +
      (9 / 4 * epsilon : k) • c
    ∃ i3 : k,
      Fce = C (Fce.coeff 0) ∧
        Rce = (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3 ∧
          FiveToSixQZeroFceZeroDeltaDescent68 gamma epsilon i3 A B c d =
            ((72 : k) * Fce.coeff 0) • (c + C ((3 / 2 : k) * gamma)) := by
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let Rce := (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
    (3 / 2 : k) • d ^ 2 + (9 / 2 * gamma : k) • e +
    (9 / 4 * epsilon : k) • c
  have hnxt :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  rcases hnxt.2.1 with ⟨i4, i3, hFce, hRce, hRceDeg⟩
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have halg :=
    fiveToSix_qZero_Fce_Rce_Delta_descent_algebra68
      gamma epsilon i3 A B c d e
  dsimp only at halg
  have hRce' : Rce = (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3 :=
    hRce
  have hK :
      FiveToSixQZeroFceZeroDeltaDescent68 gamma epsilon i3 A B c d =
        ((72 : k) * Fce.coeff 0) • (c + C ((3 / 2 : k) * gamma)) := by
    have hdiff :
        Rce - (3 / 4 * gamma : k) • B ^ 2 - (9 / 8 : k) • C i3 = 0 := by
      rw [hRce', sub_sub, sub_self]
    have hright :
        ((72 : k) • c + (108 * gamma : k) • (1 : k[X])) * Fce =
          ((72 : k) * Fce.coeff 0) • (c + C ((3 / 2 : k) * gamma)) := by
      conv_lhs => rw [hFconst]
      simp only [smul_eq_C_mul, mul_add, add_mul, mul_one]
      have h1 : C (72 : k) * c * C (Fce.coeff 0) =
          C ((72 : k) * Fce.coeff 0) * c := by
        rw [mul_right_comm, ← C_mul]
      have h2 : C (108 * gamma) * C (Fce.coeff 0) =
          C ((72 : k) * Fce.coeff 0) * C ((3 / 2 : k) * gamma) := by
        rw [← C_mul, ← C_mul]
        congr 1
        ring
      rw [h1, h2]
    have hleft :
        FiveToSixQZeroFceZeroDeltaDescent68 gamma epsilon i3 A B c d +
            (24 : k) •
              (B *
                (Rce - (3 / 4 * gamma : k) • B ^ 2 - (9 / 8 : k) • C i3)) =
          ((72 : k) • c + (108 * gamma : k) • (1 : k[X])) * Fce :=
      halg
    rw [hdiff, mul_zero, smul_zero, add_zero] at hleft
    exact hleft.trans hright
  exact ⟨i3, hFconst, hRce', hK⟩

/-! ## `J` degree on this wall -/

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_J_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
    J.natDegree ≤ p := by
  let D := 3 * N - 2 * S
  let p := 2 * N
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  have hloaded := hs.1
  rcases hloaded with ⟨hsupport, hrows⟩
  rcases hsupport with ⟨hstop, hTD⟩
  rcases hstop with ⟨hcur, ht, hstate, hclass, hraw0, hraw2⟩
  let T := S - 2 * D
  let t := min D T
  have htT : t = T := by dsimp only [t]; exact Nat.min_eq_right hTD
  have hstate' := hstate
  dsimp only [FiveToSixCuspZetaFirstB3EqualityPostEpsilonState68] at hstate'
  have hjidx : 5 * N - 2 * S - (t - 1) - 1 = p := by
    dsimp only [D, T] at htT
    dsimp only [p]
    omega
  rw [hjidx] at hstate'
  exact hstate'.2

/-! ## Charged discriminant degree and top -/

/-- The `Fce_0` side of (S1) has degree `Cc`, below the Rest top, so
`deg Δ ≤ 3D+Cc-V` on this chamber as well. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree ≤
      3 * D + Cc - V := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let M := 3 * D + Cc
  change Delta.natDegree ≤ M - V
  have hdesc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_descent68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hdesc
  rcases hdesc with ⟨i3, hFconst, hRce, hK⟩
  let Rest' := FiveToSixQZeroFceZeroDeltaRest68 gamma epsilon i3 B c d
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrestSource⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hv : V = 5 * N - G - S := by dsimp only [V]; omega
  have hdcoeff : d.coeff V ≠ 0 := by rw [hv]; exact hdtop
  have hdne : d ≠ 0 := by
    intro hdz
    subst d
    exact hdcoeff rfl
  have hddeg : d.natDegree = V :=
    natDegree_eq_of_le_of_coeff_ne_zero hd' hdcoeff
  have hRest : Rest'.natDegree ≤ M := by
    dsimp only [Rest', FiveToSixQZeroFceZeroDeltaRest68, M]
    compute_degree <;> omega
  have hdecomp :
      (24 : k) • (d * Delta) + Rest' =
        ((72 : k) * (((((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
            (3 / 2 * gamma : k) • d +
            (3 / 4 * epsilon : k) • B).coeff 0))) •
          (c + C ((3 / 2 : k) * gamma)) := by
    dsimp only [FiveToSixQZeroFceZeroDeltaDescent68] at hK
    dsimp only [Delta, Rest', FiveToSixQZeroFceZeroDeltaRest68]
    linear_combination hK
  have hRHS :
      (((72 : k) *
            (((((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
                (3 / 2 * gamma : k) • d +
                (3 / 4 * epsilon : k) • B).coeff 0))) •
          (c + C ((3 / 2 : k) * gamma))).natDegree ≤ M := by
    have hCcM : Cc ≤ M := by dsimp only [D, Cc, M]; omega
    compute_degree <;> omega
  have hscaled : ((24 : k) • (d * Delta)).natDegree ≤ M := by
    have hsub :
        (24 : k) • (d * Delta) =
          (((72 : k) *
                (((((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
                    (3 / 2 * gamma : k) • d +
                    (3 / 4 * epsilon : k) • B).coeff 0))) •
              (c + C ((3 / 2 : k) * gamma))) -
            Rest' := by
      linear_combination hdecomp
    rw [hsub]
    exact (natDegree_sub_le _ _).trans (max_le hRHS hRest)
  rw [natDegree_smul _ (by norm_num : (24 : k) ≠ 0)] at hscaled
  by_cases hDelta : Delta = 0
  · rw [hDelta, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_mul hdne hDelta, hddeg] at hscaled
    omega

/-- The degree-`M` coefficient of the charged descent never sees `Fce_0`.
The resultant then pins `Δ_(3D+Cc-V) = 3 B_D d_V ≠ 0`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_top68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let L := 3 * D + Cc - V
    (fiveToSixCuspDiscriminantPolynomial68 A B c).coeff L =
        (3 : k) * B.coeff D * d.coeff V ∧
      (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree = L := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let M := 3 * D + Cc
  let L := M - V
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  change Delta.coeff L = (3 : k) * B.coeff D * d.coeff V ∧ Delta.natDegree = L
  have hdesc :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_descent68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hdesc
  rcases hdesc with ⟨i3, hFconst, hRce, hK⟩
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrestSource⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hwall
  rcases hwall with ⟨hEq, hDpos, hDp, hDwin, hpU, hCcU, hKV, hND, hNV,
    hA', hB', hc', hd', he', ha0, hb0, hD0⟩
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hdtop
  have hDelta : Delta.natDegree ≤ L :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hM : V ≤ M := by dsimp only [D, Cc, V, M]; omega
  have hVL : V + L = M := by dsimp only [L]; omega
  have hB3deg : (B ^ 3).natDegree ≤ 3 * D := by compute_degree; omega
  have hB3 : (B ^ 3).coeff (3 * D) = B.coeff D ^ 3 := by
    have h := coeff_pow_at_bound68 B D 3 hB'
    simpa only [Nat.mul_comm] using h
  have hB3c : (B ^ 3 * c).coeff M = B.coeff D ^ 3 * c.coeff Cc := by
    have h := coeff_mul_at_bounds68 (B ^ 3) c (3 * D) Cc hB3deg hc'
    rw [show 3 * D + Cc = M by rfl, hB3] at h
    exact h
  have hd2deg : (d ^ 2).natDegree ≤ 2 * V := by compute_degree; omega
  have hd2 : (d ^ 2).coeff (2 * V) = d.coeff V ^ 2 := by
    have h := coeff_pow_at_bound68 d V 2 hd'
    simpa only [Nat.mul_comm] using h
  have hBd2 : (B * d ^ 2).coeff M = B.coeff D * d.coeff V ^ 2 := by
    have h := coeff_mul_at_bounds68 B (d ^ 2) D (2 * V) hB' hd2deg
    rw [show D + 2 * V = M by dsimp only [D, Cc, V, M]; omega, hd2] at h
    exact h
  have hdDelta : (d * Delta).coeff M = d.coeff V * Delta.coeff L := by
    have h := coeff_mul_at_bounds68 d Delta V L hd' hDelta
    rw [hVL] at h
    exact h
  have hB3low : (B ^ 3).natDegree < M := by dsimp only [D, Cc, M] at *; omega
  have hBlow : B.natDegree < M := by dsimp only [D, Cc, M] at *; omega
  have hcdlow : (c * d).natDegree < M := by
    compute_degree; dsimp only [D, Cc, V, M] at *; omega
  have hdlow : d.natDegree < M := by dsimp only [D, Cc, V, M] at *; omega
  have hclow : c.natDegree < M := by dsimp only [D, Cc, M] at *; omega
  have hCglow : (c + C ((3 / 2 : k) * gamma)).natDegree < M := by
    have := natDegree_add_le c (C ((3 / 2 : k) * gamma))
    have hC : (C ((3 / 2 : k) * gamma)).natDegree = 0 := natDegree_C _
    omega
  have hcoeff :=
    congrArg (fun P : k[X] => P.coeff M) hK
  dsimp only [FiveToSixQZeroFceZeroDeltaDescent68] at hcoeff
  have hMpos : 0 < M := by dsimp only [D, Cc, M]; omega
  have hcM : c.coeff M = 0 := coeff_eq_zero_of_natDegree_lt hclow
  have hCM : (C ((3 / 2 : k) * gamma)).coeff M = 0 := by
    rw [coeff_C]
    split_ifs with hM0
    · omega
    · rfl
  simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hB3c,
    hBd2, coeff_eq_zero_of_natDegree_lt hB3low,
    coeff_eq_zero_of_natDegree_lt hBlow,
    coeff_eq_zero_of_natDegree_lt hcdlow,
    coeff_eq_zero_of_natDegree_lt hdlow, mul_zero, add_zero, sub_zero,
    coeff_zero, hcM, hCM] at hcoeff
  rw [hdDelta] at hcoeff
  have htop :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).2
  have hrel :
      d.coeff V * (Delta.coeff L - (3 : k) * B.coeff D * d.coeff V) = 0 := by
    linear_combination (1 / 24 : k) * hcoeff - (1 / 6 : k) * B.coeff D * htop
  have hdelta : Delta.coeff L = (3 : k) * B.coeff D * d.coeff V := by
    have hz : Delta.coeff L - (3 : k) * B.coeff D * d.coeff V = 0 :=
      (mul_eq_zero.mp hrel).resolve_left hdcoeff
    linear_combination hz
  refine ⟨hdelta, ?_⟩
  apply natDegree_eq_of_le_of_coeff_ne_zero hDelta
  rw [hdelta]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hbcoeff) hdcoeff

/-! ## Charged `H` degree -/

/-- With `deg Δ ≤ 3D+Cc-V` and `deg J ≤ p`, (S2) drops `H` to degree
`D+p-Cc` (`N` on this wall).  The charged term `3 d Fce_0` has degree
`V`, below that top. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_degree68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    (FiveToSixQZeroFceZeroH68 B c d).natDegree ≤ D + p - Cc := by
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let J := (B * c ^ 2 - (1 / 9 : k) • (A * B ^ 3)) - (3 : k) • (d * e)
  let H := FiveToSixQZeroFceZeroH68 B c d
  let M := D + p
  change H.natDegree ≤ M - Cc
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrestSource⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
  have hc' : c.natDegree ≤ Cc := by dsimp only [Cc]; omega
  have hd' : d.natDegree ≤ V := by dsimp only [V]; omega
  have hcidx : Cc = 4 * N - G := by dsimp only [Cc]; omega
  have hccoeff : c.coeff Cc ≠ 0 := by rw [hcidx]; exact hctop
  have hcne : c ≠ 0 := by
    intro hcz
    subst c
    exact hccoeff rfl
  have hcdeg : c.natDegree = Cc :=
    natDegree_eq_of_le_of_coeff_ne_zero hc' hccoeff
  have hDelta : Delta.natDegree ≤ 3 * D + Cc - V :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hJ : J.natDegree ≤ p :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_J_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have halg :=
    fiveToSix_qZero_Fce_J_Delta_H_algebra68 gamma epsilon A B c d e
  change B * J = -(1 / 9 : k) • (B ^ 2 * Delta) + (1 / 3 : k) • (c * H) -
      (1 / 3 : k) • (B ^ 3 * d) + (9 / 2 * gamma : k) • d ^ 2 +
      (9 / 4 * epsilon : k) • (B * d) - (3 : k) • (d * Fce) at halg
  have hiso :
      (1 / 3 : k) • (c * H) =
        B * J + (1 / 9 : k) • (B ^ 2 * Delta) + (1 / 3 : k) • (B ^ 3 * d) -
          (9 / 2 * gamma : k) • d ^ 2 - (9 / 4 * epsilon : k) • (B * d) +
          (3 : k) • (d * Fce) := by
    rw [halg]
    module
  have hscaled : ((1 / 3 : k) • (c * H)).natDegree ≤ M := by
    rw [hiso, hFconst]
    dsimp only [M]
    compute_degree <;> omega
  rw [natDegree_smul _ (by norm_num : (1 / 3 : k) ≠ 0)] at hscaled
  by_cases hHz : H = 0
  · rw [hHz, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_mul hcne hHz, hcdeg] at hscaled
    omega

/-! ## I4 in comparison coordinates -/

/-- Matching through `D` rewrites `Fce=C(Fce_0)` as an identity in the
comparison polynomials.  The right-hand side has degree `3D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_comparison_I468
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let Rc := C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c
    let Re := C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d
    B * Re - d * Rc =
      C (B.coeff D) *
        ((1 / 9 : k) • B ^ 3 - (3 / 2 * gamma : k) • d -
          (3 / 4 * epsilon : k) • B +
          C ((((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
              (3 / 2 * gamma : k) • d +
              (3 / 4 * epsilon : k) • B).coeff 0)) := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let Fce := ((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
    (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B
  let Rc := C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c
  let Re := C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d
  have hFconst :
      Fce = C (Fce.coeff 0) :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_constant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have halg :=
    fiveToSix_qZero_comparison_Be_cd_algebra68 B c d e N D Cc
  have hBe :
      B * e + c * d =
        (1 / 9 : k) • B ^ 3 - (3 / 2 * gamma : k) • d -
          (3 / 4 * epsilon : k) • B + C (Fce.coeff 0) := by
    have hF : Fce = C (Fce.coeff 0) := hFconst
    dsimp only [Fce] at hF
    linear_combination hF
  have hmul := congrArg (fun P : k[X] => C (B.coeff D) * P) hBe
  dsimp only [Rc, Re]
  rw [halg]
  exact hmul

/-! ## Residual packet

The comparison remainders after matching through `D` still have degree
at most `N-1` and `E-D-1`.  The charged profiles add exact degree
`3D+Cc-V` for `Δ` (top `3 B_D d_V`) and `deg H ≤ N`.  These are not
`r_c=r_e=0`. -/
def FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingARemainderClosureResidual68
    (gamma epsilon : k) (A B c d e : k[X]) (N S : ℕ) : Prop :=
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  (C (c.coeff Cc) * X ^ N * B - C (B.coeff D) * c).natDegree ≤ N - 1 ∧
    (C (B.coeff D) * e + C (c.coeff Cc) * X ^ N * d).natDegree ≤
      E - D - 1 ∧
    (fiveToSixCuspDiscriminantPolynomial68 A B c).natDegree =
      3 * D + Cc - V ∧
    (fiveToSixCuspDiscriminantPolynomial68 A B c).coeff (3 * D + Cc - V) =
      (3 : k) * B.coeff D * d.coeff V ∧
    (FiveToSixQZeroFceZeroH68 B c d).natDegree ≤ N

theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_closure68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroVanishingARemainderClosureResidual68
      gamma epsilon A B c d e N S := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let p := 2 * N
  have hprop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_proportionality_through_D68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq
  dsimp only at hprop
  have htop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_top68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at htop
  have hH :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_degree68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hH
  have hwall :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_wall_index68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hEq : 9 * N = 7 * S := hwall.1
  refine ⟨hprop.2.1, hprop.2.2, ?_, ?_, ?_⟩
  · simpa [D, Cc, V] using htop.2
  · simpa [D, Cc, V] using htop.1
  · have hle : D + p - Cc ≤ N := by
      dsimp only [D, p, Cc]
      omega
    exact hH.trans hle

/-- The committed zero-remainder comparison still requires the extra
identities `R_c=R_e=0`, which the residual above does not supply. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_zero_remainder_still_impossible68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hBc0 : C (c.coeff (4 * N - 2 * S)) * X ^ N * B -
      C (B.coeff (3 * N - 2 * S)) * c = 0)
    (hEd0 : C (B.coeff (3 * N - 2 * S)) * e +
      C (c.coeff (4 * N - 2 * S)) * X ^ N * d = 0) :
    False :=
  fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_zero_remainder_impossible68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
    hterminal hs hq hBc0 hEd0

#print axioms fiveToSix_qZero_comparison_Be_cd_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_charged_descent68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_J_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_Delta_top68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_H_degree68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_comparison_I468
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_remainder_closure68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_zero_remainder_still_impossible68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingARemainderClosure68

end Max11DegreeRoutes
