import Sol68ScaleTwoAlignedSquareTerminalGNonzeroBackwireScratch

/-! # Factoring and retaining the vanishing `I₄` load on the `G[-1]` wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGQuadraticWall68

variable {k : Type*} [Field k] [CharZero k]

private abbrev terminalGScalar68 (gamma c : k) : k := 2 * c + 3 * gamma

/-- The quadratic wall and the canonical `I₃` face recover the terminal,
hence `I₄`, leading face. -/
theorem rhoOneDoubleZero_gQuadraticWall_fourFace68
    (gamma a b c f g : k) (ha : a ≠ 0)
    (hwall : 3 * terminalGScalar68 gamma c ^ 2 + 4 * a * b ^ 2 = 0)
    (hi3 : rhoOneZeroLCubicDoubleZeroGZeroThree68 gamma a b c f g = 0) :
    rhoOneZeroLCubicDoubleZeroGZeroFour68 gamma b c f g = 0 := by
  simp only [rhoOneZeroLCubicDoubleZeroGZeroThree68] at hi3
  simp only [rhoOneZeroLCubicDoubleZeroGZeroFour68, terminalGScalar68]
  by_cases hb : b = 0
  · subst b
    have hSsq : (2 * c + 3 * gamma) ^ 2 = 0 := by
      linear_combination (1 / 3 : k) * hwall
    have hS : 2 * c + 3 * gamma = 0 := sq_eq_zero_iff.mp hSsq
    rw [hS]
    ring
  · have hab : 2 * a * b ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
    have hmul : (2 * a * b) *
        (f * (2 * c + 3 * gamma) + 2 * b * g) = 0 := by
      calc
        (2 * a * b) * (f * (2 * c + 3 * gamma) + 2 * b * g) =
            -(2 * c + 3 * gamma) *
                (-2 * a * b * f + 3 * g * (2 * c + 3 * gamma)) +
              g * (3 * (2 * c + 3 * gamma) ^ 2 + 4 * a * b ^ 2) := by ring
        _ = 0 := by rw [hi3, hwall]; ring
    have := (mul_eq_zero.mp hmul).resolve_left hab
    simpa [add_comm] using this

/-- On the quadratic wall the affine boundary is exactly the `B[1]`
boundary; neither zero branch is discarded. -/
theorem rhoOneDoubleZero_gQuadraticWall_boundary_iff68
    (gamma a b c : k) (ha : a ≠ 0)
    (hwall : 3 * terminalGScalar68 gamma c ^ 2 + 4 * a * b ^ 2 = 0) :
    b = 0 ↔ terminalGScalar68 gamma c = 0 := by
  constructor
  · intro hb
    subst b
    have hSsq : terminalGScalar68 gamma c ^ 2 = 0 := by
      linear_combination (1 / 3 : k) * hwall
    exact sq_eq_zero_iff.mp hSsq
  · intro hS
    rw [hS] at hwall
    norm_num at hwall
    exact hwall.resolve_left ha

/-- Over the algebraic closure, the nonboundary part of the quadratic wall
is the union of two explicit rays.  The square root is included in the
packet rather than chosen implicitly. -/
theorem rhoOneDoubleZero_gQuadraticWall_explicit_rays68
    [IsAlgClosed k] (gamma a b c : k) (ha : a ≠ 0)
    (hwall : 3 * terminalGScalar68 gamma c ^ 2 + 4 * a * b ^ 2 = 0) :
    (b = 0 ∧ terminalGScalar68 gamma c = 0) ∨
      (b ≠ 0 ∧ terminalGScalar68 gamma c ≠ 0 ∧
        ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * a ∧
          (3 * terminalGScalar68 gamma c = 2 * r * b ∨
           3 * terminalGScalar68 gamma c = -(2 * r * b))) := by
  by_cases hb : b = 0
  · left
    exact ⟨hb, (rhoOneDoubleZero_gQuadraticWall_boundary_iff68
      gamma a b c ha hwall).mp hb⟩
  · right
    have hS : terminalGScalar68 gamma c ≠ 0 := by
      intro hzero
      exact hb ((rhoOneDoubleZero_gQuadraticWall_boundary_iff68
        gamma a b c ha hwall).mpr hzero)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (-3 * a)
      (by norm_num : 0 < 2)
    have hr0 : r ≠ 0 := by
      intro hrz
      subst r
      norm_num at hr
      exact ha hr
    have hfactor :
        (3 * terminalGScalar68 gamma c - 2 * r * b) *
          (3 * terminalGScalar68 gamma c + 2 * r * b) = 0 := by
      calc
        (3 * terminalGScalar68 gamma c - 2 * r * b) *
            (3 * terminalGScalar68 gamma c + 2 * r * b) =
          9 * terminalGScalar68 gamma c ^ 2 - 4 * r ^ 2 * b ^ 2 := by ring
        _ = 3 * (3 * terminalGScalar68 gamma c ^ 2 + 4 * a * b ^ 2) := by
          rw [hr]
          ring
        _ = 0 := by rw [hwall]; ring
    refine ⟨hb, hS, r, hr0, hr, ?_⟩
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · exact Or.inl (sub_eq_zero.mp hminus)
    · exact Or.inr (eq_neg_of_add_eq_zero_left hplus)

/-- Exact source residual after using the next first integral: the nonzero
`G[-1]` child has zero ground `I₄` load and is a boundary or one of two
explicit square-root rays.  The already-backwired `G[-1]=0` child is
preserved verbatim. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGFactoredResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C := rhoOneCDefectHahn68 A
      (ratFuncAtHahn46 T.root T.source.C0)
    let F := rhoOneTangentDDefectHahn68 A B
      (ratFuncAtHahn46 T.root T.source.D)
    let G := rhoOneTangentEDefectHahn68 A C
      (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
    ((∃ i4 : k,
        firstIntegralFour68 0 T.source.A T.source.B T.source.C0
          T.source.D T.source.E (RatFunc.C (0 : k))
          (RatFunc.C T.source.gamma) (RatFunc.C (0 : k))
          (RatFunc.C T.source.epsilon) (RatFunc.C (0 : k)) = RatFunc.C i4 ∧
        i4 = 0 ∧
        ((B.coeff (1 : ℚ) = 0 ∧
            terminalGScalar68 T.source.gamma (C.coeff (0 : ℚ)) = 0) ∨
          (B.coeff (1 : ℚ) ≠ 0 ∧
            terminalGScalar68 T.source.gamma (C.coeff (0 : ℚ)) ≠ 0 ∧
            ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2 : ℚ) ∧
              (3 * terminalGScalar68 T.source.gamma (C.coeff (0 : ℚ)) =
                  2 * r * B.coeff (1 : ℚ) ∨
               3 * terminalGScalar68 T.source.gamma (C.coeff (0 : ℚ)) =
                  -(2 * r * B.coeff (1 : ℚ)))))) ∨
      (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
        (RhoOneDoubleZeroRefinedGZeroTerminalBGainChild68
            T.source.gamma B C F ∨
         RhoOneDoubleZeroRefinedGZeroTerminalFGainChild68
            T.source.gamma B C F))) := by
  dsimp only
  have hnext := T.rhoOne_exceptional_doubleZero_refined_gZero
    P hB hC hF hG hbeta hdelta hzeta
  dsimp only at hnext
  rcases hnext with ⟨_, _, _, _, hi4pack, hi3, hsplit⟩
  rcases hsplit with hGne | ⟨hGzero, hG0, htail⟩
  · left
    have hwall :=
      T.rhoOne_exceptional_doubleZero_gNonzero_terminal_quadraticWall
        hp hH hp6 hp5 hp4 P hB hC hF hG hGne hi3 hbeta hdelta hzeta
    dsimp only at hwall
    let a := (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ)
    let b := (ratFuncAtHahn46 T.root T.source.B).coeff (1 : ℚ)
    let c := (rhoOneCDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff (0 : ℚ)
    let f := (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (0 : ℚ)
    let gg := (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-1 : ℚ)
    have ha : a ≠ 0 := by simpa only [a] using P.2.2.1
    have hfour : rhoOneZeroLCubicDoubleZeroGZeroFour68
        T.source.gamma b c f gg = 0 := by
      exact rhoOneDoubleZero_gQuadraticWall_fourFace68
        T.source.gamma a b c f gg ha (by simpa only [a, b, c] using hwall)
          (by simpa only [a, b, c, f, gg] using hi3)
    rcases hi4pack with ⟨i4, hi4source, hi4face⟩
    have hi4zero : i4 = 0 := by
      rw [hi4face, hfour]
      ring
    refine ⟨i4, hi4source, hi4zero, ?_⟩
    have hrays := rhoOneDoubleZero_gQuadraticWall_explicit_rays68
      T.source.gamma a b c ha (by simpa only [a, b, c] using hwall)
    simpa only [a, b, c] using hrays
  · right
    refine ⟨hGzero, hG0, ?_⟩
    have hres :=
      T.rhoOne_exceptional_doubleZero_refinedGZero_terminalBGainResidual
        hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta
    dsimp only [RhoOneDoubleZeroRefinedGZeroTerminalBGainResidual68] at hres
    rcases hres with hbad | ⟨_, _, htail'⟩
    · exact (hbad hGzero).elim
    · exact htail'

end AlignedSquareTerminalGQuadraticWall68

end Max11DegreeRoutes
