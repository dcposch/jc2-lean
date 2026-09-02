import Sol68ScaleTwoAlignedSquareBoundarySelectorsTerminalMinorScratch

/-! # The singular minor wall on the aligned-square `G[-2]` boundary -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGQuadraticWall68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- On the singular minor wall, the stored compatibility determinant loses
the two unresolved coefficients and becomes this exact `Q0,R0` scalar. -/
theorem rhoOne_boundaryG_quadraticWall_determinant_reduce68
    (a b f gm g c q r p : k) (hg : g ≠ 0)
    (hscalar : 3 * f + a * b = 0)
    (hwall : a ^ 3 * b ^ 2 + 27 * gm ^ 2 = 0)
    (hdet : p * ((-(8 / 9 : k)) * a * f * f - (8 / 3 : k) * gm * gm) -
      (-27 * c * g ^ 2) * (q * f - (8 / 3 : k) * gm * r) +
      (27 * b * g ^ 2) *
        (q * gm - (-(8 / 9 : k)) * a * f * r) = 0) :
    9 * q * a * b * c - 27 * q * b * gm + 8 * r * a ^ 2 * b ^ 2 +
      72 * r * c * gm = 0 := by
  have hn := rhoOne_boundaryG_minor_normalize68 a b f gm hscalar
  rw [hwall] at hn
  have h81 : (81 : k) ≠ 0 := by norm_num
  have hD : (-(8 / 9 : k)) * a * f * f - (8 / 3 : k) * gm * gm = 0 := by
    exact (mul_eq_zero.mp (by simpa using hn)).resolve_left h81
  have hmul : g ^ 2 *
      (9 * q * a * b * c - 27 * q * b * gm + 8 * r * a ^ 2 * b ^ 2 +
        72 * r * c * gm) = 0 := by
    linear_combination
      g ^ 2 * (9 * q * c + 8 * r * a * b) * hscalar - hdet + p * hD
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hg)

/-- The singular wall is either its honest coordinate endpoint or one of
two explicit square-root rays.  No root is selected without a witness. -/
theorem rhoOne_boundaryG_quadraticWall_explicit_rays68
    (a b f gm : k) (ha : a ≠ 0)
    (hscalar : 3 * f + a * b = 0)
    (hwall : a ^ 3 * b ^ 2 + 27 * gm ^ 2 = 0) :
    (b = 0 ∧ f = 0 ∧ gm = 0) ∨
      (b ≠ 0 ∧ gm ≠ 0 ∧ ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * a ∧
        ((27 * gm = r ^ 3 * b ∧ r * f = 3 * gm) ∨
         (27 * gm = -(r ^ 3 * b) ∧ r * f = -(3 * gm)))) := by
  by_cases hb : b = 0
  · left
    have hf : f = 0 := by
      rw [hb] at hscalar
      linear_combination (1 / 3 : k) * hscalar
    have hgm2 : gm ^ 2 = 0 := by
      rw [hb] at hwall
      linear_combination (1 / 27 : k) * hwall
    exact ⟨hb, hf, sq_eq_zero_iff.mp hgm2⟩
  · right
    have hgm : gm ≠ 0 := by
      intro hgm
      rw [hgm] at hwall
      norm_num at hwall
      exact hwall.elim ha hb
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (-3 * a)
      (by norm_num : 0 < 2)
    have hr0 : r ≠ 0 := by
      intro hrz
      subst r
      norm_num at hr
      exact ha hr
    have hfactor : (r ^ 3 * b - 27 * gm) * (r ^ 3 * b + 27 * gm) = 0 := by
      calc
        (r ^ 3 * b - 27 * gm) * (r ^ 3 * b + 27 * gm) =
            (r ^ 2) ^ 3 * b ^ 2 - 729 * gm ^ 2 := by ring
        _ = -27 * (a ^ 3 * b ^ 2 + 27 * gm ^ 2) := by rw [hr]; ring
        _ = 0 := by rw [hwall]; ring
    refine ⟨hb, hgm, r, hr0, hr, ?_⟩
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · left
      have hray : r ^ 3 * b = 27 * gm := sub_eq_zero.mp hminus
      refine ⟨hray.symm, ?_⟩
      linear_combination
        (1 / 27 : k) *
          (9 * r * hscalar - 3 * r * b * hr + 3 * hray)
    · right
      have hray : r ^ 3 * b = -(27 * gm) := eq_neg_of_add_eq_zero_left hplus
      refine ⟨?_, ?_⟩
      · linear_combination hray
      · linear_combination
          (1 / 27 : k) *
            (9 * r * hscalar - 3 * r * b * hr + 3 * hray)

/-- Exact source-preserving refinement of the singular minor.  The old
nonsingular transport is retained verbatim; the singular limb now carries
both its reduced determinant and its finite endpoint/ray classification. -/
def RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let Q0 := (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 2 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 1 +
        (A.coeff (-1) * B.coeff 3 + A.coeff 0 * B.coeff 2) * F.coeff 0) +
    (8 / 3 : k) * (C.coeff 1 * G.coeff 1 + C.coeff 2 * G.coeff 0 +
      C.coeff 4 * G.coeff (-2)) +
    (4 / 3 : k) * (2 * F.coeff 0 * F.coeff 2 + F.coeff 1 ^ 2) +
    2 * T.source.epsilon * C.coeff 2
  let R0 := B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
    B.coeff 5 * G.coeff (-2) + C.coeff 1 * F.coeff 2 +
    C.coeff 2 * F.coeff 1 + (3 / 4 : k) * T.source.epsilon * B.coeff 3
  let D := (-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 ^ 2 -
    (8 / 3 : k) * G.coeff (-1) ^ 2
  RhoOneAlignedSquareGNegTwoBoundaryMinor68 T g u ∧
  ((A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 = 0 ∧
      9 * Q0 * A.coeff (-2) * B.coeff 2 * C.coeff 1 -
          27 * Q0 * B.coeff 2 * G.coeff (-1) +
          8 * R0 * A.coeff (-2) ^ 2 * B.coeff 2 ^ 2 +
          72 * R0 * C.coeff 1 * G.coeff (-1) = 0 ∧
      ((B.coeff 2 = 0 ∧ F.coeff 0 = 0 ∧ G.coeff (-1) = 0) ∨
       (B.coeff 2 ≠ 0 ∧ G.coeff (-1) ≠ 0 ∧
        ∃ r : k, r ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
          ((27 * G.coeff (-1) = r ^ 3 * B.coeff 2 ∧
              r * F.coeff 0 = 3 * G.coeff (-1)) ∨
           (27 * G.coeff (-1) = -(r ^ 3 * B.coeff 2) ∧
              r * F.coeff 0 = -(3 * G.coeff (-1))))))) ∨
    (A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0 ∧
      D ≠ 0 ∧
      D * B.coeff 4 = (8 / 3 : k) * G.coeff (-1) * R0 - Q0 * F.coeff 0 ∧
      D * C.coeff 3 = G.coeff (-1) * Q0 -
        (-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 * R0))

theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_quadraticResidual68
    {p q : k[X][X]} {j : k} {h0 g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (R : RhoOneAlignedSquareGNegTwoBoundaryMinor68 T g u) :
    RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u := by
  have Rc := R
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rc
  rcases Rc with ⟨Rtf, hsplit⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3old, i4old, hi3src, hi4src, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hterminal⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨R0, hi3zero, hterminalOld⟩
  have R0c := R0
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at R0c
  rcases R0c with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hf, hg, hb1, hS, hscalar, hi4face⟩
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
  let F := rhoOneTangentDDefectHahn68 A B
    (ratFuncAtHahn46 T.root T.source.D)
  let G := rhoOneTangentEDefectHahn68 A C
    (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
  let P0 := A.coeff (-2) ^ 3 * B.coeff 2 ^ 3 * C.coeff 1 -
      9 * A.coeff (-2) ^ 2 * B.coeff 2 ^ 3 * G.coeff (-1) +
      9 * A.coeff (-2) * A.coeff (-1) * B.coeff 2 ^ 3 * G.coeff (-2) -
      18 * A.coeff (-2) * B.coeff 2 * C.coeff 1 ^ 2 * G.coeff (-1) +
      9 * A.coeff (-2) * B.coeff 2 * C.coeff 1 * C.coeff 2 * G.coeff (-2) +
      9 * A.coeff (-1) * B.coeff 2 * C.coeff 1 ^ 2 * G.coeff (-2) +
      27 * B.coeff 2 * C.coeff 1 * G.coeff (-1) ^ 2 +
      27 * B.coeff 2 * C.coeff 2 * G.coeff (-2) * G.coeff (-1)
  let Q0 := (-(8 / 9 : k)) *
      (A.coeff (-2) * B.coeff 2 * F.coeff 2 +
        (A.coeff (-2) * B.coeff 3 + A.coeff (-1) * B.coeff 2) * F.coeff 1 +
        (A.coeff (-1) * B.coeff 3 + A.coeff 0 * B.coeff 2) * F.coeff 0) +
    (8 / 3 : k) * (C.coeff 1 * G.coeff 1 + C.coeff 2 * G.coeff 0 +
      C.coeff 4 * G.coeff (-2)) +
    (4 / 3 : k) * (2 * F.coeff 0 * F.coeff 2 + F.coeff 1 ^ 2) +
    2 * T.source.epsilon * C.coeff 2
  let R0 := B.coeff 2 * G.coeff 1 + B.coeff 3 * G.coeff 0 +
    B.coeff 5 * G.coeff (-2) + C.coeff 1 * F.coeff 2 +
    C.coeff 2 * F.coeff 1 + (3 / 4 : k) * T.source.epsilon * B.coeff 3
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68]
  refine ⟨R, ?_⟩
  rcases hsplit with hwall | hnon
  · left
    have hdet' : P0 *
        ((-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 * F.coeff 0 -
          (8 / 3 : k) * G.coeff (-1) * G.coeff (-1)) -
        (-27 * C.coeff 1 * G.coeff (-2) ^ 2) *
          (Q0 * F.coeff 0 - (8 / 3 : k) * G.coeff (-1) * R0) +
        (27 * B.coeff 2 * G.coeff (-2) ^ 2) *
          (Q0 * G.coeff (-1) -
            (-(8 / 9 : k)) * A.coeff (-2) * F.coeff 0 * R0) = 0 := by
      dsimp only [A, B, C, F, G, P0, Q0, R0] at hdet ⊢
      convert hdet using 1 <;> ring
    have hred := rhoOne_boundaryG_quadraticWall_determinant_reduce68
      (A.coeff (-2)) (B.coeff 2) (F.coeff 0) (G.coeff (-1))
      (G.coeff (-2)) (C.coeff 1) Q0 R0 P0 hg hscalar hwall hdet'
    have hrays := rhoOne_boundaryG_quadraticWall_explicit_rays68
      (A.coeff (-2)) (B.coeff 2) (F.coeff 0) (G.coeff (-1))
      P.2.2.1 hscalar hwall
    dsimp only [A, B, C, F, G, P0, Q0, R0] at hwall hred hrays ⊢
    exact ⟨hwall, hred, hrays⟩
  · right
    exact hnon

end AlignedSquareBoundaryGQuadraticWall68

end Max11DegreeRoutes
