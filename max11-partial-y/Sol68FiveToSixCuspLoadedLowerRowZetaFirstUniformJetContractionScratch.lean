import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformFiniteRecurrenceScratch

/-! # Jet contraction of the bounded zeta-first recurrence

The uniform source family is converted into fixed-bound reflected jets.
The I3/I4 finite sum is split at its newest coefficient, giving a genuinely
triangular recurrence.  Each of its five load products is contracted at its
exact threshold, and the three lower rows are transported to fixed-bound jet
coordinates.  The endpoint `m=S-q` remains explicit.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetContraction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A coefficient in the reflection at a fixed support bound. -/
def FixedReflectedJet68 (p : k[X]) (u r : ℕ) : k :=
  (p.reflect u).coeff r

/-- Ordinary finite convolution of two fixed-bound reflected jet strings. -/
def FixedReflectedJetConvolution68
    (p : k[X]) (u : ℕ) (r : k[X]) (v depth : ℕ) : k :=
  ∑ j ∈ Finset.range (depth+1),
    FixedReflectedJet68 p u j * FixedReflectedJet68 r v (depth-j)

/-- Original and reflected coefficients agree at a fixed bounded depth. -/
theorem coeff_top_sub_eq_fixedReflectedJet68
    (p : k[X]) (u depth : ℕ) (hdepth : depth ≤ u) :
    p.coeff (u-depth) = FixedReflectedJet68 p u depth := by
  dsimp only [FixedReflectedJet68]
  rw [coeff_reflect,revAt_le hdepth]

/-- Multiplication is finite convolution in fixed reflected coordinates. -/
theorem fixedReflectedJet_mul68
    (p r : k[X]) (u v depth : ℕ)
    (hp : p.natDegree ≤ u) (hr : r.natDegree ≤ v) :
    FixedReflectedJet68 (p*r) (u+v) depth =
      FixedReflectedJetConvolution68 p u r v depth := by
  have h := congrArg (fun z : k[X] ↦ z.coeff depth)
    (reflect_mul p r hp hr)
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [FixedReflectedJet68,FixedReflectedJetConvolution68] using h

/-- A derivative jet is the corresponding original jet times its exact
falling linear weight. -/
theorem fixedReflectedJet_derivative68
    (p : k[X]) (u depth : ℕ) (hdepth : depth < u) :
    FixedReflectedJet68 (derivative p) (u-1) depth =
      (((u-depth : ℕ) : k)) * FixedReflectedJet68 p u depth := by
  dsimp only [FixedReflectedJet68]
  rw [coeff_reflect,revAt_le (by omega),coeff_derivative,
    coeff_reflect,revAt_le (by omega)]
  have hi : u-1-depth+1 = u-depth := by omega
  have hik : (((u-1-depth : ℕ) : k) + 1) = ((u-depth : ℕ) : k) := by
    have hcast := congrArg (fun n : ℕ ↦ (n : k)) hi
    simpa only [Nat.cast_add,Nat.cast_one] using hcast
  rw [hi,hik]
  ring

/-- The five non-discriminant terms in the uniform I3/I4 equation. -/
def FiveToSixCuspZetaFirstFiveLoadExpression68
    (gamma : k) (B c d e : k[X]) (idx : ℕ) : k :=
  (2/3 : k) * (B^3*c).coeff idx -
    (3/2 : k) * (B*d^2).coeff idx +
    (9/2*gamma : k) * ((c*d).coeff idx - (B*e).coeff idx) +
    (3/4*gamma : k) * (B^3).coeff idx

/-- Exact threshold-aware contractions of all five I3/I4 load products.
Before a threshold the coefficient is zero; at and after it the coefficient
is its finite reflected convolution at the shifted depth. -/
def FiveToSixCuspZetaFirstFiveLoadJetContractions68
    (B c d e : k[X]) (N G S t : ℕ) : Prop :=
  let U := 8*N-2*G
  let V := 5*N-G-S
  let idx := U+V-t
  let bU := 3*N-G
  let cU := 4*N-G
  let eU := 6*N-G-S
  ((B^3*c).coeff idx =
      if G-S ≤ t then
        FixedReflectedJetConvolution68
          (B^3) (3*bU) c cU (t-(G-S))
      else 0) ∧
    ((B*d^2).coeff idx =
      if S ≤ t then
        FixedReflectedJetConvolution68 B bU (d^2) (2*V) (t-S)
      else 0) ∧
    ((c*d).coeff idx =
      if 4*N-G ≤ t then
        FixedReflectedJetConvolution68 c cU d V (t-(4*N-G))
      else 0) ∧
    ((B*e).coeff idx =
      if 4*N-G ≤ t then
        FixedReflectedJetConvolution68 B bU e eU (t-(4*N-G))
      else 0) ∧
    ((B^3).coeff idx =
      if 4*N-S ≤ t then
        FixedReflectedJetConvolution68 (B^2) (2*bU) B bU (t-(4*N-S))
      else 0)

/-- Source degree bounds contract every one of the five loads at every
depth through `S`; all threshold coincidences are retained by the `if`s. -/
theorem fiveToSix_zetaFirst_fiveLoad_jet_contractions68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S t : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (htS : t ≤ S) :
    FiveToSixCuspZetaFirstFiveLoadJetContractions68 B c d e N G S t := by
  let R := 7*N-2*G
  let mu := min S (R-S)
  let U := 8*N-2*G
  let V := 5*N-G-S
  let idx := U+V-t
  let bU := 3*N-G
  let cU := 4*N-G
  let eU := 6*N-G-S
  change 0 < S ∧ S < R ∧ d.natDegree ≤ V ∧
      e.natDegree ≤ eU ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ R-S < S ∧ mu = R-S ∧ zeta = 0 ∧ _ at hs
  rcases hs with ⟨hS,hSR,hd,he,hp,hless,hmu,hz,hzero,hsupp⟩
  rcases hp with ⟨hn,hgt,hle,hA,hB,hc,hd0,he0,ha,hcusp,had⟩
  have hB2 : (B^2).natDegree ≤ 2*bU := by
    dsimp only [bU]
    compute_degree
    omega
  have hB3 : (B^3).natDegree ≤ 3*bU := by
    dsimp only [bU]
    compute_degree
    omega
  have hd2 : (d^2).natDegree ≤ 2*V := by
    compute_degree
    omega
  change FiveToSixCuspZetaFirstFiveLoadJetContractions68 B c d e N G S t
  dsimp only [FiveToSixCuspZetaFirstFiveLoadJetContractions68,U,V,idx,bU,cU,eU]
  constructor
  · by_cases hload : G-S ≤ t
    · rw [if_pos hload]
      have hdepth : t-(G-S) ≤ 3*(3*N-G)+(4*N-G) := by omega
      rw [show U+V-t =
          (3*(3*N-G)+(4*N-G))-(t-(G-S)) by omega,
        coeff_top_sub_eq_fixedReflectedJet68 _ _ _ hdepth,
        fixedReflectedJet_mul68 (B^3) c (3*(3*N-G)) (4*N-G)
          (t-(G-S)) hB3 hc]
    · rw [if_neg hload]
      apply coeff_eq_zero_of_natDegree_lt
      have hb : (B^3*c).natDegree ≤ 3*(3*N-G)+(4*N-G) := by
        compute_degree
        omega
      exact hb.trans_lt (by omega)
  constructor
  · by_cases hload : S ≤ t
    · rw [if_pos hload]
      have hdepth : t-S ≤ (3*N-G)+2*(5*N-G-S) := by omega
      rw [show U+V-t =
          ((3*N-G)+2*(5*N-G-S))-(t-S) by omega,
        coeff_top_sub_eq_fixedReflectedJet68 _ _ _ hdepth,
        fixedReflectedJet_mul68 B (d^2) (3*N-G) (2*(5*N-G-S))
          (t-S) hB hd2]
    · rw [if_neg hload]
      apply coeff_eq_zero_of_natDegree_lt
      have hb : (B*d^2).natDegree ≤ (3*N-G)+2*(5*N-G-S) := by
        compute_degree
        omega
      exact hb.trans_lt (by omega)
  constructor
  · by_cases hload : 4*N-G ≤ t
    · rw [if_pos hload]
      have hdepth : t-(4*N-G) ≤ (4*N-G)+(5*N-G-S) := by omega
      rw [show U+V-t =
          ((4*N-G)+(5*N-G-S))-(t-(4*N-G)) by omega,
        coeff_top_sub_eq_fixedReflectedJet68 _ _ _ hdepth,
        fixedReflectedJet_mul68 c d (4*N-G) (5*N-G-S)
          (t-(4*N-G)) hc hd]
    · rw [if_neg hload]
      apply coeff_eq_zero_of_natDegree_lt
      have hb : (c*d).natDegree ≤ (4*N-G)+(5*N-G-S) := by
        compute_degree
        omega
      exact hb.trans_lt (by omega)
  constructor
  · by_cases hload : 4*N-G ≤ t
    · rw [if_pos hload]
      have hdepth : t-(4*N-G) ≤ (3*N-G)+(6*N-G-S) := by omega
      rw [show U+V-t =
          ((3*N-G)+(6*N-G-S))-(t-(4*N-G)) by omega,
        coeff_top_sub_eq_fixedReflectedJet68 _ _ _ hdepth,
        fixedReflectedJet_mul68 B e (3*N-G) (6*N-G-S)
          (t-(4*N-G)) hB he]
    · rw [if_neg hload]
      apply coeff_eq_zero_of_natDegree_lt
      have hb : (B*e).natDegree ≤ (3*N-G)+(6*N-G-S) := by
        compute_degree
        omega
      exact hb.trans_lt (by omega)
  · by_cases hload : 4*N-S ≤ t
    · rw [if_pos hload]
      have hdepth : t-(4*N-S) ≤ 2*(3*N-G)+(3*N-G) := by omega
      rw [show U+V-t =
          (2*(3*N-G)+(3*N-G))-(t-(4*N-S)) by omega,
        coeff_top_sub_eq_fixedReflectedJet68 _ _ _ hdepth]
      simpa only [pow_succ,pow_two,mul_assoc] using
        fixedReflectedJet_mul68 (B^2) B (2*(3*N-G)) (3*N-G)
          (t-(4*N-S)) hB2 hB
    · rw [if_neg hload]
      apply coeff_eq_zero_of_natDegree_lt
      have hb : (B^3).natDegree ≤ 2*(3*N-G)+(3*N-G) := by
        compute_degree
        omega
      exact hb.trans_lt (by omega)

/-- The uniform I3/I4 equation solved for its newest discriminant jet.
This is triangular without dividing by the nonzero cusp-edge coefficient. -/
def FiveToSixCuspZetaFirstTriangularJetScalar68
    (gamma : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := q+m
  let idx := U+V-t
  (Delta.reflect U).coeff t * (d.reflect V).coeff 0 =
    -((∑ j ∈ Finset.Ico q t,
        (Delta.reflect U).coeff j * (d.reflect V).coeff (t-j)) +
      FiveToSixCuspZetaFirstFiveLoadExpression68 gamma B c d e idx)

theorem fiveToSix_zetaFirst_uniform_scalar_triangular68
    (gamma : k) (A B c d e : k[X]) (N G S q m : ℕ)
    (hscalar : FiveToSixCuspZetaFirstLoadedUniformScalar68
      gamma A B c d e N G S q m) :
    FiveToSixCuspZetaFirstTriangularJetScalar68
      gamma A B c d e N G S q m := by
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8*N-2*G
  let V := 5*N-G-S
  let t := q+m
  let idx := U+V-t
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformScalar68] at hscalar
  have hqt : q ≤ t := by dsimp only [t]; omega
  rw [Finset.sum_Ico_succ_top hqt] at hscalar
  change FiveToSixCuspZetaFirstTriangularJetScalar68
    gamma A B c d e N G S q m
  dsimp only [FiveToSixCuspZetaFirstTriangularJetScalar68,
    FiveToSixCuspZetaFirstFiveLoadExpression68,Delta,U,V,t,idx]
  have hi : q+m-(q+m)=0 := by omega
  rw [hi] at hscalar
  linear_combination hscalar

/-- Row-zero written at one common fixed reflected bound. -/
def FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let W := 13*N-2*G-S-1
  let t := q+m
  FixedReflectedJet68 (secondaryResidualRowZeroPolynomial68 A B c d e) W t +
      (2/9*gamma : k) * FixedReflectedJet68 (B*derivative A*c) W t +
      (2/3*gamma : k) * FixedReflectedJet68 (B*derivative e) W t -
      (1/9*epsilon : k) * FixedReflectedJet68 (A*B*derivative A) W t -
      (2/9*gamma : k) * FixedReflectedJet68 (A*derivative A*d) W t -
      (2/3*gamma : k) * FixedReflectedJet68 (d*derivative c) W t -
      (1/3*epsilon : k) * FixedReflectedJet68 (d*derivative A) W t = 0

/-- Row-one written at one common fixed reflected bound. -/
def FiveToSixCuspZetaFirstUniformJetRowOneScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let W := 12*N-2*G-S-1
  let t := q+m
  FixedReflectedJet68 (secondaryResidualRowOnePolynomial68 A B c d e) W t +
      (4/3*gamma : k) * FixedReflectedJet68 (A*derivative e) W t -
      (4/3*gamma : k) * FixedReflectedJet68 (c*derivative c) W t +
      (2/9*gamma : k) * FixedReflectedJet68 (derivative A*B^2) W t +
      (2/3*gamma : k) * FixedReflectedJet68 (B*derivative d) W t -
      (2/3*gamma : k) * FixedReflectedJet68 (d*derivative B) W t +
      (2/3*epsilon : k) * FixedReflectedJet68 (A*derivative c) W t +
      (2*epsilon : k) * FixedReflectedJet68 (derivative e) W t = 0

/-- Row-two written at one common fixed reflected bound. -/
def FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ) : Prop :=
  let W := 11*N-2*G-S-1
  let t := q+m
  FixedReflectedJet68 (secondaryResidualRowTwoPolynomial68 A B c d e) W t +
      (4/3*gamma : k) * FixedReflectedJet68 (A*derivative d) W t -
      (4/3*gamma : k) * FixedReflectedJet68 (B*derivative c) W t -
      (4/3*gamma : k) * FixedReflectedJet68 (c*derivative B) W t -
      (2/3*gamma : k) * FixedReflectedJet68 (d*derivative A) W t -
      (1/3*epsilon : k) * FixedReflectedJet68 (derivative A*B) W t +
      (2/3*epsilon : k) * FixedReflectedJet68 (A*derivative B) W t +
      (2*epsilon : k) * FixedReflectedJet68 (derivative d) W t = 0

/-- Exact transport of all three lower rows to fixed reflected jets. -/
theorem fiveToSix_zetaFirst_uniform_rows_jet_contraction68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q m : ℕ)
    (hN : 0 < N) (hgt : 5*N < 2*G) (hle : 2*G ≤ 6*N)
    (hS : 0 < S) (hSR : S < 7*N-2*G) (hqm : q+m ≤ S)
    (h0 : FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68
      gamma epsilon A B c d e N G S q m)
    (h1 : FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68
      gamma epsilon A B c d e N G S q m)
    (h2 : FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68
      gamma epsilon A B c d e N G S q m) :
    FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstUniformJetRowOneScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
        gamma epsilon A B c d e N G S q m := by
  let t := q+m
  let W0 := 13*N-2*G-S-1
  let W1 := 12*N-2*G-S-1
  let W2 := 11*N-2*G-S-1
  have ht0 : t ≤ W0 := by dsimp only [t,W0]; omega
  have ht1 : t ≤ W1 := by dsimp only [t,W1]; omega
  have ht2 : t ≤ W2 := by dsimp only [t,W2]; omega
  have hi0 : 13*N-2*G-S-(q+m)-1 = W0-t := by
    dsimp only [W0,t]
    omega
  have hi1 : 12*N-2*G-S-(q+m)-1 = W1-t := by
    dsimp only [W1,t]
    omega
  have hi2 : 11*N-2*G-S-(q+m)-1 = W2-t := by
    dsimp only [W2,t]
    omega
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowZeroScalar68] at h0
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowOneScalar68] at h1
  dsimp only [FiveToSixCuspZetaFirstLoadedUniformRowTwoScalar68] at h2
  rw [hi0] at h0
  rw [hi1] at h1
  rw [hi2] at h2
  change (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (W0-t) +
      (2/9*gamma : k) * (B*derivative A*c).coeff (W0-t) +
      (2/3*gamma : k) * (B*derivative e).coeff (W0-t) -
      (1/9*epsilon : k) * (A*B*derivative A).coeff (W0-t) -
      (2/9*gamma : k) * (A*derivative A*d).coeff (W0-t) -
      (2/3*gamma : k) * (d*derivative c).coeff (W0-t) -
      (1/3*epsilon : k) * (d*derivative A).coeff (W0-t) = 0 at h0
  change (secondaryResidualRowOnePolynomial68 A B c d e).coeff (W1-t) +
      (4/3*gamma : k) * (A*derivative e).coeff (W1-t) -
      (4/3*gamma : k) * (c*derivative c).coeff (W1-t) +
      (2/9*gamma : k) * (derivative A*B^2).coeff (W1-t) +
      (2/3*gamma : k) * (B*derivative d).coeff (W1-t) -
      (2/3*gamma : k) * (d*derivative B).coeff (W1-t) +
      (2/3*epsilon : k) * (A*derivative c).coeff (W1-t) +
      (2*epsilon : k) * (derivative e).coeff (W1-t) = 0 at h1
  change (secondaryResidualRowTwoPolynomial68 A B c d e).coeff (W2-t) +
      (4/3*gamma : k) * (A*derivative d).coeff (W2-t) -
      (4/3*gamma : k) * (B*derivative c).coeff (W2-t) -
      (4/3*gamma : k) * (c*derivative B).coeff (W2-t) -
      (2/3*gamma : k) * (d*derivative A).coeff (W2-t) -
      (1/3*epsilon : k) * (derivative A*B).coeff (W2-t) +
      (2/3*epsilon : k) * (A*derivative B).coeff (W2-t) +
      (2*epsilon : k) * (derivative d).coeff (W2-t) = 0 at h2
  repeat' first
    | rw [coeff_top_sub_eq_fixedReflectedJet68 _ _ _ ht0] at h0
    | rw [coeff_top_sub_eq_fixedReflectedJet68 _ _ _ ht1] at h1
    | rw [coeff_top_sub_eq_fixedReflectedJet68 _ _ _ ht2] at h2
  change FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
      gamma epsilon A B c d e N G S q m ∧
    FiveToSixCuspZetaFirstUniformJetRowOneScalar68
      gamma epsilon A B c d e N G S q m ∧
    FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
      gamma epsilon A B c d e N G S q m
  dsimp only [FiveToSixCuspZetaFirstUniformJetRowZeroScalar68,
    FiveToSixCuspZetaFirstUniformJetRowOneScalar68,
    FiveToSixCuspZetaFirstUniformJetRowTwoScalar68,W0,W1,W2,t]
  exact ⟨h0,h1,h2⟩

/-- The complete bounded triangular recurrence and contracted lower rows. -/
def FiveToSixCuspZetaFirstUniformJetRecurrence68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  ∀ m, m ≤ S-q →
    FiveToSixCuspZetaFirstTriangularJetScalar68
        gamma A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstFiveLoadJetContractions68
        B c d e N G S (q+m) ∧
      FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstUniformJetRowOneScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
        gamma epsilon A B c d e N G S q m

theorem fiveToSix_zetaFirst_uniform_jet_recurrence68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S q : ℕ)
    (hs : FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S)
    (hqS : q ≤ S)
    (hfamily : FiveToSixCuspZetaFirstLoadedUniformFiniteFamily68
      gamma epsilon A B c d e N G S q) :
    FiveToSixCuspZetaFirstUniformJetRecurrence68
      gamma epsilon A B c d e N G S q := by
  have hsrc := hs
  change 0 < S ∧ S < 7*N-2*G ∧ _ ∧ _ ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hsrc
  have hp := hsrc.2.2.2.2.1
  change 0 < N ∧ 5*N < 2*G ∧ 2*G ≤ 6*N ∧ _ at hp
  intro m hm
  have hqm : q+m ≤ S := by omega
  rcases hfamily m hm with ⟨hi,h0,h1,h2⟩
  have hrows := fiveToSix_zetaFirst_uniform_rows_jet_contraction68
    gamma epsilon A B c d e N G S q m
    hp.1 hp.2.1 hp.2.2.1 hsrc.1 hsrc.2.1 hqm h0 h1 h2
  exact ⟨fiveToSix_zetaFirst_uniform_scalar_triangular68
      gamma A B c d e N G S q m hi,
    fiveToSix_zetaFirst_fiveLoad_jet_contractions68
      alpha gamma epsilon zeta eta terminal A B c d e N G S (q+m)
      hs hqm,
    hrows.1,hrows.2.1,hrows.2.2⟩

/-- Literal finite endpoint: the bounded recurrence reaches `t=S`. -/
def FiveToSixCuspZetaFirstUniformJetEndpoint68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) : Prop :=
  ∃ m, m = S-q ∧ q+m = S ∧
    FiveToSixCuspZetaFirstTriangularJetScalar68
        gamma A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstFiveLoadJetContractions68
        B c d e N G S S ∧
      FiveToSixCuspZetaFirstUniformJetRowZeroScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstUniformJetRowOneScalar68
        gamma epsilon A B c d e N G S q m ∧
      FiveToSixCuspZetaFirstUniformJetRowTwoScalar68
        gamma epsilon A B c d e N G S q m

theorem fiveToSix_zetaFirst_uniform_jet_endpoint68
    (gamma epsilon : k) (A B c d e : k[X])
    (N G S q : ℕ) (hqS : q ≤ S)
    (hrec : FiveToSixCuspZetaFirstUniformJetRecurrence68
      gamma epsilon A B c d e N G S q) :
    FiveToSixCuspZetaFirstUniformJetEndpoint68
      gamma epsilon A B c d e N G S q := by
  let m := S-q
  have hqm : q+m = S := by dsimp only [m]; omega
  have h := hrec m (le_refl _)
  refine ⟨m,rfl,hqm,h.1,?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  simpa only [hqm] using h.2.1

/-- Source-facing residual with the exact least-q witness, full bounded
triangular recurrence, and its endpoint attached. -/
def FiveToSixCuspZetaFirstUniformJetContractionResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  FiveToSixCuspZetaFirstUniformFiniteRecurrenceResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧
    ∃ q, min S (7*N-2*G-S) < q ∧ q ≤ S ∧
      (∀ j, j < q →
        ((fiveToSixCuspDiscriminantPolynomial68 A B c).reflect
          (8*N-2*G)).coeff j = 0) ∧
      FiveToSixCuspZetaFirstUniformJetRecurrence68
        gamma epsilon A B c d e N G S q ∧
      FiveToSixCuspZetaFirstUniformJetEndpoint68
        gamma epsilon A B c d e N G S q

theorem fiveToSix_zetaFirst_uniform_jet_contraction_residual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hu : FiveToSixCuspZetaFirstUniformFiniteRecurrenceResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S) :
    FiveToSixCuspZetaFirstUniformJetContractionResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S := by
  refine ⟨hu,?_⟩
  rcases hu.2 with ⟨q,hmuq,hqS,hprior,hminimal,hload,hscalar,hfamily⟩
  have hnext2 := hu.1
  have hn2 := hnext2.1
  have hn1 := hn2.1
  have hn0 := hn1.1
  have hn := hn0.1
  have hr2 := hn.1
  change FiveToSixCuspZetaFirstFiniteLoadedRowOneResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr2
  have hr1 := hr2.1
  change FiveToSixCuspZetaFirstFiniteLoadedRowZeroResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr1
  have hr0 := hr1.1
  change FiveToSixCuspZetaFirstFiniteLoadedResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hr0
  have hl := hr0.1
  change FiveToSixCuspZetaFirstFiniteStoppingResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hl
  have hf := hl.1
  change FiveToSixCuspZetaFirstDepthFiveResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hf
  have hfour := hf.1
  change FiveToSixCuspZetaFirstDepthFourResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hfour
  have hthree := hfour.1
  change FiveToSixCuspZetaFirstDepthThreeResidual68
      alpha gamma epsilon zeta eta terminal A B c d e N G S ∧ _ at hthree
  have hsupport := hthree.1
  change FiveToSixCuspZetaFirstSupportPacket68 alpha gamma epsilon zeta eta
      terminal A B c d e N G S ∧ _ at hsupport
  have hrec := fiveToSix_zetaFirst_uniform_jet_recurrence68
    alpha gamma epsilon zeta eta terminal A B c d e N G S q
    hsupport.1 hqS hfamily
  exact ⟨q,hmuq,hqS,hprior,hrec,
    fiveToSix_zetaFirst_uniform_jet_endpoint68
      gamma epsilon A B c d e N G S q hqS hrec⟩

#print axioms coeff_top_sub_eq_fixedReflectedJet68
#print axioms fixedReflectedJet_mul68
#print axioms fixedReflectedJet_derivative68
#print axioms fiveToSix_zetaFirst_fiveLoad_jet_contractions68
#print axioms fiveToSix_zetaFirst_uniform_scalar_triangular68
#print axioms fiveToSix_zetaFirst_uniform_rows_jet_contraction68
#print axioms fiveToSix_zetaFirst_uniform_jet_recurrence68
#print axioms fiveToSix_zetaFirst_uniform_jet_endpoint68
#print axioms fiveToSix_zetaFirst_uniform_jet_contraction_residual68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetContraction68

end Max11DegreeRoutes
