import Sol410ScaleTwoAlignedNonsquareComplementFinalRowScratch

/-! # Same-witness raw source packet for the complementary `(4,10)` rows -/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false

/-- The chamber constants and raw defect rows on one exact `g,f,l` witness.
Keeping this data in one structure lets later row transformations be checked
as separate opaque declarations without reselecting any existential witness. -/
structure AlignedNonsquareComplementRaw410
    {K : Type*} [Field K] [CharZero K]
    (H : K[X]) (p q : K[X][Y]) (g f l : K[X]) where
  kappa : K
  kappa3 : K
  kappa5 : K
  kappa7 : K
  kappa9 : K
  kappa11 : K
  hH : H ≠ 0
  hp3 : p.coeff 3 = H * g
  hgf : g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f
  hL : g * f + (8 : K[X]) * p.coeff 1 = H * l
  hM2 : alignedThirdDefect410 H (p.coeff 1) (p.coeff 2) (p.coeff 3)
      (q.coeff 7) kappa = 0
  hM4 : alignedFourthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 6) (q.coeff 7) kappa =
        Polynomial.C kappa3 * H ^ 6
  hM5 : alignedFifthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 5) (q.coeff 6) (q.coeff 7) kappa = 0
  hM6 : alignedSixthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7)
      kappa = Polynomial.C kappa5 * H ^ 9
  hM7 : alignedSeventhDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 3) (q.coeff 4) (q.coeff 5) (q.coeff 6)
      (q.coeff 7) kappa = 0
  hM8 : alignedEighthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 2) (q.coeff 3) (q.coeff 4) (q.coeff 5)
      (q.coeff 6) (q.coeff 7) kappa = Polynomial.C kappa7 * H ^ 12
  hM9 : alignedNinthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3) (q.coeff 4)
      (q.coeff 5) (q.coeff 6) (q.coeff 7) kappa = 0
  hM10 : alignedTenthDefect410 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
      (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) kappa =
        Polynomial.C kappa9 * H ^ 15
  hM11 : alignedEleventhDefect410 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
      (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) kappa = 0
  hM12 : alignedTwelfthDefect410 H (p.coeff 0) (p.coeff 1)
      (p.coeff 2) (p.coeff 3) (q.coeff 1) (q.coeff 2) (q.coeff 3)
      (q.coeff 4) (q.coeff 5) (q.coeff 6) (q.coeff 7) kappa =
        Polynomial.C kappa11 * H ^ 18

/-- Extract the raw packet from the normalized source and identify its
internal `g,f` with the allocation's exact witnesses by cancelling `H`. -/
theorem normalized410ScaleTwo_alignedNonsquare_complementRaw
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H g f l : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 = 0)
    (hp3 :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      p.coeff 3 = H * g)
    (hgf :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      g ^ 2 - (4 : K[X]) * p.coeff 2 = H * f)
    (hL :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      g * f + (8 : K[X]) * p.coeff 1 = H * l) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ R : AlignedNonsquareComplementRaw410 H p q g f l, True := by
  dsimp only at haligned hp3 hgf hL ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ3, κ5, κ7, κ9, κ11, g0, f0, hp30, hM2, hM4,
      hM5, hM6, hM7, hM8, hM9, hM10, hM11, hM12, hgf0, _hblock12⟩ :=
    normalized410ScaleTwo_alignedTwelfthRow_nonsquareChamber_packet
      hsource hnsq haligned
  have hg0 : g0 = g := by
    apply mul_left_cancel₀ hsource.1
    calc
      H * g0 = p.coeff 3 := hp30.symm
      _ = H * g := hp3
  subst g
  have hf0 : f0 = f := by
    apply mul_left_cancel₀ hsource.1
    calc
      H * f0 = g0 ^ 2 - (4 : K[X]) * p.coeff 2 := hgf0.symm
      _ = H * f := hgf
  subst f
  refine ⟨{
    kappa := κ, kappa3 := κ3, kappa5 := κ5, kappa7 := κ7,
    kappa9 := κ9, kappa11 := κ11, hH := hsource.1,
    hp3 := hp3, hgf := hgf, hL := hL, hM2 := hM2, hM4 := hM4,
    hM5 := hM5, hM6 := hM6, hM7 := hM7, hM8 := hM8, hM9 := hM9,
    hM10 := hM10, hM11 := hM11, hM12 := hM12 }, trivial⟩

#print axioms normalized410ScaleTwo_alignedNonsquare_complementRaw

end Max11DegreeRoutes
