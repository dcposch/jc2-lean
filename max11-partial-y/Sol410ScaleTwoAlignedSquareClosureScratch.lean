import Sol410ScaleTwoAlignedSquareP1DivisorClosureScratch

/-! # Closure of the aligned-square `(4,10)` face

The first global allocation `h0 | p1` is already impossible.  On the sole
remaining allocation, `u=h0^2*g1` and `p2=h0^3*r2`; revisiting the exact
ninth quotient and cancelling one further literal `h0` leaves
`327680*p1(root)^3`.  This contradicts the same-witness nonvanishing of
`p1(root)` and closes the face.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

variable {K : Type*} [Field K] [CharZero K]

/-- Exact quotient of the ninth load on `g=h0*g1`, `r=h0^2*r2` after
cancelling the remaining literal `h0`.  Its root value is
`327680*p1(root)^3`. -/
def alignedSquareDeepGRNinthLoad410
    (h0 g1 r2 p0 p1 q1 : K[X])
    (κ μ κ3 μ2 κ5 μ3 κ7 μ4 : K) : K[X] :=
  (327680 : K[X]) * p1 ^ 3 + h0 *
    (-(43008 : K[X]) * Polynomial.C μ * p1 ^ 2 + h0 *
    ((262144 : K[X]) * Polynomial.C κ * p0 * p1 -
      (512 : K[X]) * Polynomial.C κ5 * p1 - (1048576 : K[X]) * q1 + h0 *
    (-(2560 : K[X]) * Polynomial.C μ2 * p0 +
      (1966080 : K[X]) * p0 * p1 * r2 -
      (640 : K[X]) * Polynomial.C μ2 * g1 * p1 -
      (491520 : K[X]) * g1 * p1 ^ 2 * r2 -
      (6144 : K[X]) * Polynomial.C κ3 * p1 * r2 - Polynomial.C μ4 + h0 *
    ((983040 : K[X]) * p0 ^ 2 * g1 -
      (491520 : K[X]) * p0 * g1 ^ 2 * p1 -
      (6144 : K[X]) * Polynomial.C κ3 * p0 * g1 -
      (86016 : K[X]) * Polynomial.C μ * p0 * r2 +
      (122880 : K[X]) * g1 ^ 3 * p1 ^ 2 +
      (1536 : K[X]) * Polynomial.C κ3 * g1 ^ 2 * p1 -
      (4 : K[X]) * Polynomial.C κ7 * g1 +
      (21504 : K[X]) * Polynomial.C μ * g1 * p1 * r2 -
      (24 : K[X]) * Polynomial.C μ3 * r2 + h0 *
    ((10752 : K[X]) * Polynomial.C μ * p0 * g1 ^ 2 -
      (4480 : K[X]) * Polynomial.C μ * g1 ^ 3 * p1 +
      (3 : K[X]) * Polynomial.C μ3 * g1 ^ 2 -
      (320 : K[X]) * Polynomial.C μ2 * r2 ^ 2 -
      (163840 : K[X]) * p1 * r2 ^ 3 + h0 *
    (-(491520 : K[X]) * p0 * g1 * r2 ^ 2 +
      (240 : K[X]) * Polynomial.C μ2 * g1 ^ 2 * r2 +
      (368640 : K[X]) * g1 ^ 2 * p1 * r2 ^ 2 +
      (1536 : K[X]) * Polynomial.C κ3 * g1 * r2 ^ 2 +
      (3584 : K[X]) * Polynomial.C μ * r2 ^ 3 + h0 *
    ((245760 : K[X]) * p0 * g1 ^ 3 * r2 -
      (153600 : K[X]) * g1 ^ 4 * p1 * r2 -
      (768 : K[X]) * Polynomial.C κ3 * g1 ^ 3 * r2 -
      (6720 : K[X]) * Polynomial.C μ * g1 ^ 2 * r2 ^ 2 -
      (35 : K[X]) * Polynomial.C μ2 * g1 ^ 4 + h0 *
    (-(30720 : K[X]) * p0 * g1 ^ 5 +
      (17920 : K[X]) * g1 ^ 6 * p1 +
      (96 : K[X]) * Polynomial.C κ3 * g1 ^ 5 +
      (2520 : K[X]) * Polynomial.C μ * g1 ^ 4 * r2 +
      (61440 : K[X]) * g1 * r2 ^ 4 + h0 *
    (-(273 : K[X]) * Polynomial.C μ * g1 ^ 6 -
      (102400 : K[X]) * g1 ^ 3 * r2 ^ 3 + h0 *
    ((53760 : K[X]) * g1 ^ 5 * r2 ^ 2 + h0 *
    (-(11520 : K[X]) * g1 ^ 7 * r2 + h0 *
      ((880 : K[X]) * g1 ^ 9))))))))))))

set_option maxHeartbeats 8000000 in
/-- The sole surviving deeper-divisor allocation contradicts the ninth row
at the exact supplied root. -/
theorem alignedSquareDeepGR_ninthFalse410
    (H h0 u g1 r2 p0 p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 : K[X])
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
    (hu : u = h0 ^ 2 * g1) (hp2 : p2 = h0 ^ 3 * r2)
    (x : K) (hx : h0.eval x = 0) (hp1x : p1.eval x ≠ 0) : False := by
  have hcore := alignedSquareNinth_core_410 hh0 hHsq hp3 hM2 hM4 hM6
    hM8 hM10 hM12 hM14
  have hu' : u = h0 * (h0 * g1) := by rw [hu]; ring
  have hp2' : p2 = h0 * (h0 ^ 2 * r2) := by rw [hp2]; ring
  rw [hu', hp2'] at hcore
  have hload : alignedSquareUFactorNinthLoad410 h0 (h0 * g1)
      (h0 ^ 2 * r2) p0 p1 q1 κ μ κ3 μ2 κ5 μ3 κ7 μ4 = 0 := by
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
  have hfactor : alignedSquareUFactorNinthLoad410 h0 (h0 * g1)
      (h0 ^ 2 * r2) p0 p1 q1 κ μ κ3 μ2 κ5 μ3 κ7 μ4 =
      h0 * alignedSquareDeepGRNinthLoad410 h0 g1 r2 p0 p1 q1
        κ μ κ3 μ2 κ5 μ3 κ7 μ4 := by
    simp only [alignedSquareUFactorNinthLoad410,
      alignedSquareDeepGRNinthLoad410]
    ring
  rw [hfactor] at hload
  have hdeep : alignedSquareDeepGRNinthLoad410 h0 g1 r2 p0 p1 q1
      κ μ κ3 μ2 κ5 μ3 κ7 μ4 = 0 :=
    (mul_eq_zero.mp hload).resolve_left hh0
  have hdeepx := congrArg (fun w : K[X] => w.eval x) hdeep
  simp only [alignedSquareDeepGRNinthLoad410, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat] at hdeepx
  rw [hx] at hdeepx
  norm_num at hdeepx
  exact hp1x hdeepx

section Source410

variable [IsAlgClosed K]

/-- The aligned-square source face is impossible, with the supplied `h0`
and all packet witnesses preserved exactly. -/
theorem normalized410ScaleTwo_alignedSquare_false
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0) : False := by
  dsimp only at haligned
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨x, u, _v, g, r, r1, g1, r2, hx, hp1x, hp3, _hv, hu, hp2, hr,
    hg, hr1⟩ := normalized410ScaleTwo_alignedSquare_sourceDeepDivisors
      hsource hh0 hHsq haligned
  have huDeep : u = h0 ^ 2 * g1 := by
    calc
      u = h0 * g := hu
      _ = h0 * (h0 * g1) := by rw [hg]
      _ = h0 ^ 2 * g1 := by ring
  have hp2Deep : p.coeff 2 = h0 ^ 3 * r2 := by
    calc
      p.coeff 2 = h0 * r := hp2
      _ = h0 * (h0 * r1) := by rw [hr]
      _ = h0 * (h0 * (h0 * r2)) := by rw [hr1]
      _ = h0 ^ 3 * r2 := by ring
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
  exact alignedSquareDeepGR_ninthFalse410
    H h0 u g1 r2 (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) κ μ κ3 μ2 κ5 μ3 κ7 μ4 hh0 hHsq hp3 hM2 hM4
      hM6 hM8 hM10 hM12 hM14 huDeep hp2Deep x hx hp1x

/-- Closed implementation of the routing adapter's aligned-square
exclusion premise. -/
theorem planeKeller410AlignedSquareExclusion_closed :
    PlaneKeller410AlignedSquareExclusion (K := K) := by
  intro P Q H h0 hsource hh0 hHsq haligned
  exact normalized410ScaleTwo_alignedSquare_false
    hsource hh0 hHsq haligned

end Source410

#print axioms alignedSquareDeepGR_ninthFalse410
#print axioms normalized410ScaleTwo_alignedSquare_false
#print axioms planeKeller410AlignedSquareExclusion_closed

end Max11DegreeRoutes
