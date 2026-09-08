import Sol410ScaleTwoAlignedSquareComplementAllocationScratch

/-! # Same-witness closure of the aligned-square complement limb -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- On the supplied `v`-root with `u` nonzero, the seventh square row kills
the odd constant `μ`.  This is separated from the later complement loads so
that the source witness is never reselected. -/
theorem alignedSquareVRoot_mu_zero410
    (H h0 u v p0 p1 p2 p3 q3 q4 q5 q6 q7 : K[X])
    (κ μ κ3 μ2 κ5 μ3 : K)
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
    (hv : u ^ 2 - (4 : K[X]) * p2 = h0 * v)
    (x : K) (hx : h0.eval x = 0)
    (hux : u.eval x ≠ 0) (hvx : v.eval x = 0) : μ = 0 := by
  have hcore := alignedSquareSeventh_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10
  obtain ⟨s, hs, _hq3⟩ := alignedSquareSeventh_solved_410 hh0 hcore hv
  have hkilla : u.eval x ^ 2 = (4 : K) * p2.eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) hv
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat] at hev
    rw [hx, zero_mul] at hev
    linear_combination hev
  have hmutie : (80 : K) * u.eval x * v.eval x ^ 3 =
      μ * ((35 : K) * u.eval x ^ 4 -
        (336 : K) * p2.eval x * u.eval x ^ 2 +
        (1344 : K) * p2.eval x ^ 2) := by
    have hev := congrArg (fun w : K[X] => w.eval x) hs
    simp only [Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_C] at hev
    rw [hx, zero_mul] at hev
    linear_combination hev
  have hkill : u.eval x *
      ((16 : K) * v.eval x ^ 3 - (7 : K) * μ * u.eval x ^ 3) = 0 := by
    linear_combination (1 / 5 : K) * hmutie -
      (336 / 5 : K) * μ * p2.eval x * hkilla
  have htail : (16 : K) * v.eval x ^ 3 -
      (7 : K) * μ * u.eval x ^ 3 = 0 :=
    (mul_eq_zero.mp hkill).resolve_left hux
  rw [hvx] at htail
  have hprod : μ * u.eval x ^ 3 = 0 := by
    linear_combination (-1 / 7 : K) * htail
  exact (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 3 hux)

set_option maxHeartbeats 8000000 in
/-- The exact square-packet witness selected by the source is impossible on
the `v(root)=0`, `u(root)≠0` limb.  All complementary rows and the final
Keller row are evaluated at the same supplied root of the same supplied
linear factor `h0`. -/
theorem normalized410ScaleTwo_alignedSquare_complement_false
    [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 u v : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hp3 :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = h0 ^ 2 * u)
    (hv :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v)
    (x : K) (hx : h0.eval x = 0)
    (hux : u.eval x ≠ 0) (hvx : v.eval x = 0) : False := by
  dsimp only at haligned hp3 hv
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hdeg : h0.natDegree = 1 := by
    have hdegree := congrArg Polynomial.natDegree hHsq
    rw [hsource.2.1, Polynomial.natDegree_pow] at hdegree
    omega
  have hpacket := normalized410ScaleTwo_alignedTwelfthRow_squareChamber_packet
    hsource hh0 hHsq haligned
  dsimp only at hpacket
  obtain ⟨κ, μ, κ3, μ2, κ5, μ3, κ7, μ4, κ9, μ5, κ11,
    u0, v0, _s16, _s25, _s26, _s27, _s28, _s29, _s30, _s31, _s32, _s33,
    hp30, hM2, hM4, hM6, hM8, hM10, hM12, hM14, hM16, hM18, hM20,
    hv0, _hq0, _hd1, _hd2, _hd3, _hd4, _hd5, _hd6, _hd7, _hd8, _hd9,
    _hpin, _hcross⟩ := hpacket
  have hu0 : u0 = u := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hh0)
    calc
      h0 ^ 2 * u0 = p.coeff 3 := hp30.symm
      _ = h0 ^ 2 * u := hp3
  subst u0
  have hv0eq : v0 = v := by
    apply mul_left_cancel₀ hh0
    calc
      h0 * v0 = u ^ 2 - (4 : K[X]) * p.coeff 2 := hv0.symm
      _ = h0 * v := hv
  subst v0
  have hmu : μ = 0 := alignedSquareVRoot_mu_zero410
    H h0 u v (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
      κ μ κ3 μ2 κ5 μ3 hh0 hHsq hp3 hM2 hM4 hM6 hM8 hM10 hv
      x hx hux hvx
  have hrootUnique : ∀ y : K, h0.eval y = 0 → y = x := by
    obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdeg
    intro y hy
    rw [← hlinear] at hx hy
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hx hy
    have hcy : c * (y - x) = 0 := by linear_combination hy - hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hcy).resolve_left hc)
  obtain ⟨f, hvf⟩ := natDegree_one_dvd_of_root_kill_410 hdeg (fun y hy => by
    rw [hrootUnique y hy]
    exact hvx)
  obtain ⟨hmu2a, l, hL⟩ := alignedSquareVFactor_complementAllocation410
    H h0 u v f (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ μ κ3 μ2 κ5 μ3 κ7 μ4 hh0 hdeg
      hHsq hp3 hM2 hM4 hM6 hM8 hM10 hM12 hM14 hv hvf hmu x hx hux
  obtain ⟨hmu2, hmu3, hmu4, hmu5, m, hLm⟩ :=
    alignedSquareComplement_oddLoads410
      H h0 u v f l (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
        (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
        (q.coeff 5) (q.coeff 6) (q.coeff 7)
        κ μ κ3 μ2 κ5 μ3 κ7 μ4 κ9 μ5 hh0 hdeg hHsq hp3 hM2 hM4
        hM6 hM8 hM10 hM12 hM14 hM16 hM18 hv hvf hL hmu x hx hux
  have hgf : u ^ 2 - (4 : K[X]) * p.coeff 2 = H * f := by
    calc
      u ^ 2 - (4 : K[X]) * p.coeff 2 = h0 * v := hv
      _ = h0 * (h0 * f) := by rw [hvf]
      _ = H * f := by rw [hHsq]; ring
  let R : AlignedNonsquareComplementRaw410 H p q u f m := {
    kappa := κ
    kappa3 := κ3
    kappa5 := κ5
    kappa7 := κ7
    kappa9 := κ9
    kappa11 := κ11
    hH := hsource.1
    hp3 := by simpa only [hHsq] using hp3
    hgf := hgf
    hL := hLm
    hM2 := by rw [hmu] at hM2; simpa using hM2
    hM4 := hM4
    hM5 := by rw [hmu2] at hM6; simpa using hM6
    hM6 := hM8
    hM7 := by rw [hmu3] at hM10; simpa using hM10
    hM8 := hM12
    hM9 := by rw [hmu4] at hM14; simpa using hM14
    hM10 := hM16
    hM11 := by rw [hmu5] at hM18; simpa using hM18
    hM12 := hM20 }
  have h9 := R.ninthRow
  have h10 := R.tenthRow
  have h11 := R.eleventhRow
  have h12 := R.twelfthRowDirect
  have hdvd := alignedSquareComplement_twelfthVDivisor_direct410
    H (p.coeff 0) u f m κ3 κ7 κ11 h11 h12
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨j, hj, hfinal⟩ :=
    normalized410ScaleTwo_alignedFinalKellerRow hsource haligned
  have hHx : H.eval x = 0 := by
    rw [hHsq, Polynomial.eval_pow, hx]
    norm_num
  exact alignedSquareComplement_finalRow_false_410
    H (p.coeff 0) (p.coeff 1) (p.coeff 2) (q.coeff 0) (q.coeff 1)
      u f m w κ κ3 κ5 κ7 κ9 κ11 j x hsource.1 hHx hLm hw h11 h12
      h9 h10 hfinal hj

#print axioms alignedSquareVRoot_mu_zero410
#print axioms normalized410ScaleTwo_alignedSquare_complement_false

end Max11DegreeRoutes
