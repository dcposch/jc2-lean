import Sol68ScaleTwoAlignedNonsquareAfterLowerOnePhiDivisorRefinedIIILoadedNinthScratch

/-! # Total-degree support audit for the normalized `(6,8)`, `H=2` leaf

The current Max-11 route is stated in partial `Y`-degree only.  If an
upstream total-degree-at-most-eleven hypothesis is retained, the scale-two
leaf is already impossible from its two leading monomials.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section CoefficientSupport68

variable {k : Type*} [Field k]

/-- A nonzero `Y^i` coefficient of `X`-degree `d` contributes the literal
monomial `X^d Y^i`, hence `d+i` is bounded by total degree. -/
theorem bivariate_coeff_natDegree_add_le_totalDegree_68
    (P : MvPolynomial (Fin 2) k) (i : ℕ)
    (hi : ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff i ≠ 0) :
    (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff i).natDegree + i ≤
      P.totalDegree := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let d : Fin 2 →₀ ℕ :=
    Finsupp.single 0 (p.coeff i).natDegree + Finsupp.single 1 i
  have hlead : (p.coeff i).coeff (p.coeff i).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hi
  have hcoeff : P.coeff d ≠ 0 := by
    rw [← bivariate_coeff_coeff_eq_mvCoeff P i (p.coeff i).natDegree]
    exact hlead
  have hd : d ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have htotal := MvPolynomial.le_totalDegree hd
  have hsum : (d.sum fun _ e => e) = (p.coeff i).natDegree + i := by
    dsimp only [d]
    rw [Finsupp.sum_add_index'] <;> simp
  rw [hsum] at htotal
  exact htotal

/-- Exact definition audit: the normalized source records only partial
`Y`-degrees, the leading core, and the Keller condition.  No total-degree or
coefficient-support hypothesis occurs in this interface. -/
theorem normalized68LeadingCoreSource_unfold_68
    (P Q : MvPolynomial (Fin 2) k) (H : k[X]) :
    Normalized68LeadingCoreSource P Q H 2 ↔
      H ≠ 0 ∧ H.natDegree = 2 ∧
      degreeOf 1 P = 6 ∧ degreeOf 1 Q = 8 ∧
      ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6 = H ^ 3 ∧
      ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8 = H ^ 4 ∧
      IsPlaneKellerPair P Q := by
  rfl

/-- The two top support monomials of a normalized scale-two source already
have total degrees at least twelve and sixteen. -/
theorem normalized68ScaleTwo_totalDegree_lower_bounds
    (P Q : MvPolynomial (Fin 2) k) (H : k[X])
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    12 ≤ P.totalDegree ∧ 16 ≤ Q.totalDegree := by
  rcases hsource with ⟨hH, hHdeg, _hPdeg, _hQdeg, hp6, hq8, _hKeller⟩
  have hp6ne :
      ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6 ≠ 0 := by
    rw [hp6]
    exact pow_ne_zero 3 hH
  have hq8ne :
      ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8 ≠ 0 := by
    rw [hq8]
    exact pow_ne_zero 4 hH
  have hp := bivariate_coeff_natDegree_add_le_totalDegree_68 P 6 hp6ne
  have hq := bivariate_coeff_natDegree_add_le_totalDegree_68 Q 8 hq8ne
  rw [hp6, natDegree_pow, hHdeg] at hp
  rw [hq8, natDegree_pow, hHdeg] at hq
  norm_num at hp hq ⊢
  exact ⟨hp, hq⟩

theorem normalized68ScaleTwo_impossible_of_totalDegree_le_eleven
    (P Q : MvPolynomial (Fin 2) k) (H : k[X])
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hPtotal : P.totalDegree ≤ 11) : False := by
  have hlow := normalized68ScaleTwo_totalDegree_lower_bounds P Q H hsource
  omega

/-- Minimal packet to thread if the intended external theorem is formulated
in total degree.  It closes `H=2` at the normalized-source boundary, so no
degree estimate for the later quotient `K` is needed. -/
def Normalized68TotalDegreeElevenSource
    (P Q : MvPolynomial (Fin 2) k) (H : k[X]) : Prop :=
  Normalized68LeadingCoreSource P Q H 2 ∧
    P.totalDegree ≤ 11 ∧ Q.totalDegree ≤ 11

theorem normalized68TotalDegreeElevenSource_impossible
    (P Q : MvPolynomial (Fin 2) k) (H : k[X])
    (hsource : Normalized68TotalDegreeElevenSource P Q H) : False := by
  exact normalized68ScaleTwo_impossible_of_totalDegree_le_eleven P Q H
    hsource.1 hsource.2.1

end CoefficientSupport68

end Max11DegreeRoutes
