import Sol410ScaleTwoAlignedSquareSourceDivisorAllocationScratch

/-! # Closure of the `h0 ∣ p1` aligned-square allocation

After the already verified second factor `p2 = h0^2 r1`, the exact ninth
quotient has root value `-1048576 q1(root)` as soon as `p1 = h0 s`.
The untouched degree-zero Keller row then vanishes at that same supplied
root.  This closes the first source-divisor allocation without changing any
source witness.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Exact quotient after additionally substituting `p2=h0^2*r1` and
`p1=h0*s` in the already verified ninth load and cancelling `h0^3`.
Its root value is `-1048576*q1(root)`. -/
def alignedSquareDeepP1NinthLoad410
    (h0 g r1 s p0 q1 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 : K) : K[X] :=
  -(1048576 : K[X]) * q1 + h0 *
    ((983040 : K[X]) * p0 ^ 2 * g - (30720 : K[X]) * p0 * g ^ 5 +
      (245760 : K[X]) * p0 * g ^ 3 * r1 +
      Polynomial.C μ * ((10752 : K[X]) * p0 * g ^ 2) -
      (491520 : K[X]) * p0 * g ^ 2 * s -
      Polynomial.C κ3 * ((6144 : K[X]) * p0 * g) -
      (491520 : K[X]) * p0 * g * r1 ^ 2 +
      Polynomial.C κ * ((262144 : K[X]) * p0 * s) -
      Polynomial.C μ * ((86016 : K[X]) * p0 * r1) -
      Polynomial.C μ2 * ((2560 : K[X]) * p0) +
      (1966080 : K[X]) * p0 * r1 * s + (880 : K[X]) * g ^ 9 -
      (11520 : K[X]) * g ^ 7 * r1 -
      Polynomial.C μ * ((273 : K[X]) * g ^ 6) +
      (17920 : K[X]) * g ^ 6 * s +
      Polynomial.C κ3 * ((96 : K[X]) * g ^ 5) +
      (53760 : K[X]) * g ^ 5 * r1 ^ 2 +
      Polynomial.C μ * ((2520 : K[X]) * g ^ 4 * r1) -
      Polynomial.C μ2 * ((35 : K[X]) * g ^ 4) -
      (153600 : K[X]) * g ^ 4 * r1 * s -
      Polynomial.C κ3 * ((768 : K[X]) * g ^ 3 * r1) -
      Polynomial.C μ * ((4480 : K[X]) * g ^ 3 * s) -
      (102400 : K[X]) * g ^ 3 * r1 ^ 3 +
      (122880 : K[X]) * g ^ 3 * s ^ 2 +
      Polynomial.C κ3 * ((1536 : K[X]) * g ^ 2 * s) -
      Polynomial.C μ * ((6720 : K[X]) * g ^ 2 * r1 ^ 2) +
      Polynomial.C μ2 * ((240 : K[X]) * g ^ 2 * r1) +
      Polynomial.C μ3 * ((3 : K[X]) * g ^ 2) +
      (368640 : K[X]) * g ^ 2 * r1 ^ 2 * s +
      Polynomial.C κ3 * ((1536 : K[X]) * g * r1 ^ 2) -
      Polynomial.C κ7 * ((4 : K[X]) * g) +
      Polynomial.C μ * ((21504 : K[X]) * g * r1 * s) -
      Polynomial.C μ2 * ((640 : K[X]) * g * s) +
      (61440 : K[X]) * g * r1 ^ 4 -
      (491520 : K[X]) * g * r1 * s ^ 2 -
      Polynomial.C κ3 * ((6144 : K[X]) * r1 * s) -
      Polynomial.C κ5 * ((512 : K[X]) * s) +
      Polynomial.C μ * ((3584 : K[X]) * r1 ^ 3) -
      Polynomial.C μ * ((43008 : K[X]) * s ^ 2) -
      Polynomial.C μ2 * ((320 : K[X]) * r1 ^ 2) -
      Polynomial.C μ3 * ((24 : K[X]) * r1) - Polynomial.C μ4 -
      (163840 : K[X]) * r1 ^ 3 * s + (327680 : K[X]) * s ^ 3)

set_option maxHeartbeats 8000000 in
/-- The ninth square quotient forces `q1` to vanish at the supplied root
once both `p2` and `p1` have acquired their recorded factors of `h0`. -/
theorem alignedSquareDeepNinth_q1RootKill410
    (H h0 u g r1 s p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 : K)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (hp3 : p3 = h0 ^ 2 * u)
    (hM2 : alignedThirdDefect410 H p1 p2 p3 q7 κ =
      Polynomial.C μ * h0 ^ 9)
    (hM4 : alignedFourthDefect410 H p0 p1 p2 p3 q6 q7 κ =
      Polynomial.C κ3 * H ^ 6)
    (hM6 : alignedFifthDefect410 H p0 p1 p2 p3 q5 q6 q7 κ =
      Polynomial.C μ2 * h0 ^ 15)
    (hM8 : alignedSixthDefect410 H p0 p1 p2 p3 q4 q5 q6 q7 κ =
      Polynomial.C κ5 * H ^ 9)
    (hM10 : alignedSeventhDefect410 H p0 p1 p2 p3 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ3 * h0 ^ 21)
    (hM12 : alignedEighthDefect410 H p0 p1 p2 p3 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C κ7 * H ^ 12)
    (hM14 : alignedNinthDefect410 H p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 κ =
      Polynomial.C μ4 * h0 ^ 27)
    (hu : u = h0 * g) (hp2 : p2 = h0 ^ 2 * r1)
    (hp1 : p1 = h0 * s)
    (x : K) (hx : h0.eval x = 0) : q1.eval x = 0 := by
  have hcore := alignedSquareNinth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14
  have hp2' : p2 = h0 * (h0 * r1) := by rw [hp2]; ring
  rw [hu, hp2', hp1] at hcore
  have hload : alignedSquareUFactorNinthLoad410 h0 g (h0 * r1) p0
      (h0 * s) q1 κ μ κ3 μ2 κ5 μ3 κ7 μ4 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 5 hh0)
    apply Polynomial.funext
    intro z
    have hz := congrArg (fun w : K[X] => w.eval z) hcore
    simp only [alignedSquareUFactorNinthLoad410, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_zero] at hz ⊢
    norm_num at hz
    linear_combination hz
  have hfactor : alignedSquareUFactorNinthLoad410 h0 g (h0 * r1) p0
      (h0 * s) q1 κ μ κ3 μ2 κ5 μ3 κ7 μ4 =
      h0 ^ 3 * alignedSquareDeepP1NinthLoad410 h0 g r1 s p0 q1
        κ μ κ3 μ2 κ5 μ3 κ7 μ4 := by
    simp only [alignedSquareUFactorNinthLoad410,
      alignedSquareDeepP1NinthLoad410]
    ring
  rw [hfactor] at hload
  have hdeep : alignedSquareDeepP1NinthLoad410 h0 g r1 s p0 q1
      κ μ κ3 μ2 κ5 μ3 κ7 μ4 = 0 :=
    (mul_eq_zero.mp hload).resolve_left (pow_ne_zero 3 hh0)
  have hloadx := congrArg (fun w : K[X] => w.eval x) hdeep
  simp only [alignedSquareDeepP1NinthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hloadx
  rw [hx] at hloadx
  norm_num at hloadx
  exact hloadx

section Source410

variable [IsAlgClosed K]

/-- The `h0 ∣ p1` allocation is impossible on the original source. -/
theorem normalized410ScaleTwo_alignedSquare_p1Divisor_false
    {P Q : MvPolynomial (Fin 2) K} {H h0 u g r1 s : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hp3 :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = h0 ^ 2 * u)
    (hu : u = h0 * g)
    (hp2 :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 2 = h0 ^ 2 * r1)
    (hp1 :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 1 = h0 * s)
    (x : K) (hx : h0.eval x = 0) : False := by
  dsimp only at haligned hp3 hp2 hp1
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpacket := normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
    hsource hh0 hHsq haligned
  dsimp only at hpacket
  obtain ⟨κ, μ, κ3, μ2, κ5, μ3, κ7, μ4, _κ9, _μ5, _κ11,
    u0, _v0, _s16, _s25, _s26, _s27, _s28, _s29, _s30, _s31, _s32, _s33,
    hp30, hM2, hM4, hM6, hM8, hM10, hM12, hM14, _hM16, _hM18, _hM20,
    _hv0, _hq0, _hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7, _hd8, _hd9,
    _hpin, _hcross⟩ := hpacket
  have hu0 : u0 = u := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 * u0 = p.coeff 3 := hp30.symm
      _ = h0 ^ 2 * u := hp3
  subst u0
  have hq1x : (q.coeff 1).eval x = 0 :=
    alignedSquareDeepNinth_q1RootKill410
      H h0 u g r1 s (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
        (q.coeff 6) (q.coeff 7) κ μ κ3 μ2 κ5 μ3 κ7 μ4 hh0 hHsq hp3
        hM2 hM4 hM6 hM8 hM10 hM12 hM14 hu hp2 hp1 x hx
  obtain ⟨j, hj, hfinal⟩ :=
    normalized410ScaleTwo_alignedFinalKellerRow hsource haligned
  have hfinalx := congrArg (fun w : K[X] => w.eval x) hfinal
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    at hfinalx
  have hp1x : (p.coeff 1).eval x = 0 := by rw [hp1, Polynomial.eval_mul, hx, zero_mul]
  rw [hq1x, hp1x] at hfinalx
  norm_num at hfinalx
  exact hj hfinalx.symm

set_option maxHeartbeats 8000000 in
/-- Only the simultaneous deeper `g`/`r1` divisor limb survives.  The
returned root and every polynomial are the exact witnesses selected by the
preceding source allocation. -/
theorem normalized410ScaleTwo_alignedSquare_sourceDeepDivisors
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    ∃ (x : K) (u v g r r1 g1 r2 : K[X]),
      h0.eval x = 0 ∧ (p.coeff 1).eval x ≠ 0 ∧
      p.coeff 3 = h0 ^ 2 * u ∧
      u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v ∧
      u = h0 * g ∧ p.coeff 2 = h0 * r ∧ r = h0 * r1 ∧
      g = h0 * g1 ∧ r1 = h0 * r2 := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  obtain ⟨x, u, v, g, r, r1, hx, hp3, hv, hu, hp2, hr, halloc⟩ :=
    normalized410ScaleTwo_alignedSquare_sourceDivisorAllocation
      hsource hh0 hHsq haligned
  have hp2deep : p.coeff 2 = h0 ^ 2 * r1 := by
    calc
      p.coeff 2 = h0 * r := hp2
      _ = h0 * (h0 * r1) := by rw [hr]
      _ = h0 ^ 2 * r1 := by ring
  rcases halloc with ⟨s, hs⟩ | ⟨g1, r2, hg, hr1⟩
  · exact (normalized410ScaleTwo_alignedSquare_p1Divisor_false
      hsource hh0 hHsq haligned hp3 hu hp2deep hs x hx).elim
  · have hdeg : h0.natDegree = 1 := by
      have hdegree := congrArg Polynomial.natDegree hHsq
      rw [hsource.2.1, Polynomial.natDegree_pow] at hdegree
      omega
    have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
      obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
      intro y hy
      rw [← hlinear] at hx hy
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] at hx hy
      have hcy : c * (y - x) = 0 := by linear_combination hy - hx
      exact sub_eq_zero.mp ((mul_eq_zero.mp hcy).resolve_left hc)
    have hp1x : (p.coeff 1).eval x ≠ 0 := by
      intro hp1x
      obtain ⟨s, hs⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
        rw [hrootUnique y hy]
        exact hp1x)
      exact normalized410ScaleTwo_alignedSquare_p1Divisor_false
        hsource hh0 hHsq haligned hp3 hu hp2deep hs x hx
    exact ⟨x, u, v, g, r, r1, g1, r2, hx, hp1x, hp3, hv, hu, hp2, hr,
      hg, hr1⟩

end Source410

#print axioms alignedSquareDeepNinth_q1RootKill410
#print axioms normalized410ScaleTwo_alignedSquare_p1Divisor_false
#print axioms normalized410ScaleTwo_alignedSquare_sourceDeepDivisors

end Max11DegreeRoutes
