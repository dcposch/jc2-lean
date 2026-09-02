import Sol68ScaleTwoAlignedSquareBoundaryGSignedRayFactorScratch

/-! # Terminal coefficient `-3` on the signed `G[-2]` rays -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareBoundaryGSignedRayTerminal68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

local instance boundaryGSignedRayTerminalLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

omit [IsAlgClosed k] in
/-- Coefficient two above the lower face of a Laurent fourfold product. -/
theorem laurent_coeff_mul_four_lower_two68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
    (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
    (X * Y * Z * W).coeff (m + n + r + s + 2) =
      X.coeff (m + 2) * Y.coeff n * Z.coeff r * W.coeff s +
      X.coeff (m + 1) * Y.coeff (n + 1) * Z.coeff r * W.coeff s +
      X.coeff (m + 1) * Y.coeff n * Z.coeff (r + 1) * W.coeff s +
      X.coeff (m + 1) * Y.coeff n * Z.coeff r * W.coeff (s + 1) +
      X.coeff m * Y.coeff (n + 2) * Z.coeff r * W.coeff s +
      X.coeff m * Y.coeff (n + 1) * Z.coeff (r + 1) * W.coeff s +
      X.coeff m * Y.coeff (n + 1) * Z.coeff r * W.coeff (s + 1) +
      X.coeff m * Y.coeff n * Z.coeff (r + 2) * W.coeff s +
      X.coeff m * Y.coeff n * Z.coeff (r + 1) * W.coeff (s + 1) +
      X.coeff m * Y.coeff n * Z.coeff r * W.coeff (s + 2) := by
  have hXYZ : (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop := by
    have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
      le_trans (by simpa using add_le_add hX hY)
        HahnSeries.orderTop_add_le_mul
    exact le_trans (by simpa using add_le_add hXY hZ)
      HahnSeries.orderTop_add_le_mul
  have h := laurent_coeff_mul_lower_two68
    (X * Y * Z) W (m + n + r) s hXYZ hW
  rw [laurent_coeff_mul_three_lower_terminal68 X Y Z m n r hX hY hZ,
    laurent_coeff_mul_three_lower_succ68 X Y Z m n r hX hY hZ,
    laurent_coeff_mul_three_lower_two68 X Y Z m n r hX hY hZ] at h
  convert h using 1 <;> ring

omit [IsAlgClosed k] in
/-- Exact terminal coefficient `-3` in the `G[-2]` order box.  Only the
next two derivative coefficients of `A` survive; all other derivative
jets are above the face. -/
theorem rhoOneMainTangentTerminal_coeff_negThree_gNegTwo68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-2 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-3 : ℤ) : WithTop ℤ) ≤ dG.orderTop)
    (hS0 : 2 * C.coeff 0 + 3 * gamma = 0) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff (-3) =
      (-(1 / 3 : k) * epsilon) * (F.coeff 0 * dA.coeff (-3)) +
      (-(4 / 9 : k)) *
        (F.coeff 2 * G.coeff (-2) * dA.coeff (-3) +
          F.coeff 1 * G.coeff (-1) * dA.coeff (-3) +
          F.coeff 1 * G.coeff (-2) * dA.coeff (-2) +
          F.coeff 0 * G.coeff 0 * dA.coeff (-3) +
          F.coeff 0 * G.coeff (-1) * dA.coeff (-2) +
          F.coeff 0 * G.coeff (-2) * dA.coeff (-1)) +
      (-(2 / 27 : k)) *
        (A.coeff (-1) * F.coeff 0 * dA.coeff (-3) * (2 * C.coeff 1) +
          A.coeff (-2) * F.coeff 1 * dA.coeff (-3) * (2 * C.coeff 1) +
          A.coeff (-2) * F.coeff 0 * dA.coeff (-2) * (2 * C.coeff 1) +
          A.coeff (-2) * F.coeff 0 * dA.coeff (-3) * (2 * C.coeff 2)) +
      (-(1 / 9 : k) * epsilon) *
        (A.coeff (-2) * B.coeff 2 * dA.coeff (-3)) +
      (-(4 / 27 : k)) *
        (A.coeff 0 * B.coeff 2 * G.coeff (-2) * dA.coeff (-3) +
          A.coeff (-1) * B.coeff 3 * G.coeff (-2) * dA.coeff (-3) +
          A.coeff (-1) * B.coeff 2 * G.coeff (-1) * dA.coeff (-3) +
          A.coeff (-1) * B.coeff 2 * G.coeff (-2) * dA.coeff (-2) +
          A.coeff (-2) * B.coeff 4 * G.coeff (-2) * dA.coeff (-3) +
          A.coeff (-2) * B.coeff 3 * G.coeff (-1) * dA.coeff (-3) +
          A.coeff (-2) * B.coeff 3 * G.coeff (-2) * dA.coeff (-2) +
          A.coeff (-2) * B.coeff 2 * G.coeff 0 * dA.coeff (-3) +
          A.coeff (-2) * B.coeff 2 * G.coeff (-1) * dA.coeff (-2) +
          A.coeff (-2) * B.coeff 2 * G.coeff (-2) * dA.coeff (-1)) := by
  let S : LaurentSeries k := 2 * C + HahnSeries.C (3 * gamma)
  have hSbase : (0 : WithTop ℤ) ≤ S.orderTop := by
    dsimp only [S]
    apply (le_min ?_ ?_).trans HahnSeries.min_orderTop_le_orderTop_add
    · rw [two_mul]
      exact (le_min hC hC).trans HahnSeries.min_orderTop_le_orderTop_add
    · by_cases hx : 3 * gamma = 0
      · rw [hx, HahnSeries.C_zero]; simp
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hx]; simp
  have hSco0 : S.coeff 0 = 0 := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single_same]
    linear_combination hS0
  have hS := laurent_orderTop_ge_succ_of_coeff_zero68 S 0 hSbase hSco0
  have hSco (n : ℤ) (hn : n ≠ 0) : S.coeff n = 2 * C.coeff n := by
    dsimp only [S]
    rw [HahnSeries.coeff_add]
    simp only [two_mul, HahnSeries.coeff_add, HahnSeries.C_apply,
      HahnSeries.coeff_single]
    rw [if_neg hn]
    ring
  have lower2 (X Y : LaurentSeries k) (m n : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
      (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have lower3 (X Y Z : LaurentSeries k) (m n r : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
      (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop :=
    lower2 (X * Y) Z (m + n) r (lower2 X Y m n hX hY) hZ
  have lower4 (X Y Z W : LaurentSeries k) (m n r s : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
      (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
      (↑(m + n + r + s) : WithTop ℤ) ≤ (X * Y * Z * W).orderTop :=
    lower2 (X * Y * Z) W (m + n + r) s
      (lower3 X Y Z m n r hX hY hZ) hW
  have zero_of_lower (X : LaurentSeries k) (n : ℤ)
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hlt : (-3 : ℤ) < n) :
      X.coeff (-3) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) hX)
  have h1 := zero_of_lower (F * dC) 0 (lower2 F dC 0 0 hF hdC) (by omega)
  have h2 := laurent_coeff_mul_lower68 F dA 0 (-3) hF hdA
  have h3 := laurent_coeff_mul_three_lower_two68 F G dA 0 (-2) (-3)
    hF hG hdA
  have h4 := zero_of_lower (F * F * dB) 0
    (lower3 F F dB 0 0 0 hF hF hdB) (by omega)
  have h5 := zero_of_lower (C * F * dC) 0
    (lower3 C F dC 0 0 0 hC hF hdC) (by omega)
  have h6 := zero_of_lower (B * dG) (-1)
    (lower2 B dG 2 (-3) hB hdG) (by omega)
  have h7 := zero_of_lower (B * F * dF) 2
    (lower3 B F dF 2 0 0 hB hF hdF) (by omega)
  have h8 := zero_of_lower (B * C * dG) (-1)
    (lower3 B C dG 2 0 (-3) hB hC hdG) (by omega)
  have h9 := zero_of_lower (B * C * dA) (-1)
    (lower3 B C dA 2 0 (-3) hB hC hdA) (by omega)
  have h10 := zero_of_lower (B * C * C * dA) (-1)
    (lower4 B C C dA 2 0 0 (-3) hB hC hC hdA) (by omega)
  have h11 := laurent_coeff_mul_four_lower_succ_terminal68
    A F dA S (-2) 0 (-3) 1 hA hF hdA hS
  have h12 := laurent_coeff_mul_three_lower_terminal68 A B dA
    (-2) 2 (-3) hA hB hdA
  have h13 := laurent_coeff_mul_four_lower_two68 A B G dA
    (-2) 2 (-2) (-3) hA hB hG hdA
  have h14 := zero_of_lower (A * B * F * dB) 0
    (lower4 A B F dB (-2) 2 0 0 hA hB hF hdB) (by omega)
  have h15 := zero_of_lower (A * B * B * dF) 2
    (lower4 A B B dF (-2) 2 2 0 hA hB hB hdF) (by omega)
  norm_num at h2 h3 h11 h12 h13
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite :
      rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F G dA dB dC dF dG =
      HahnSeries.C (-(2 / 3 : k) * gamma) * (F * dC) +
      HahnSeries.C (-(1 / 3 : k) * epsilon) * (F * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * G * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * F * dB) +
      HahnSeries.C (-(4 / 9 : k)) * (C * F * dC) +
      HahnSeries.C ((2 / 3 : k) * gamma) * (B * dG) +
      HahnSeries.C (-(4 / 9 : k)) * (B * F * dF) +
      HahnSeries.C (4 / 9 : k) * (B * C * dG) +
      HahnSeries.C ((2 / 9 : k) * gamma) * (B * C * dA) +
      HahnSeries.C (4 / 27 : k) * (B * C * C * dA) +
      HahnSeries.C (-(2 / 27 : k)) * (A * F * dA * S) +
      HahnSeries.C (-(1 / 9 : k) * epsilon) * (A * B * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * G * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * F * dB) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * B * dF) := by
    simp only [rhoOneMainTangentTerminal68, S, HahnSeries.C_eq_algebraMap,
      map_mul, map_add, map_neg, map_div₀, map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, hscale]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, hSco 1 (by norm_num), hSco 2 (by norm_num)]
  ring

omit [IsAlgClosed k] in
/-- The literal coefficient `-3` scalar after inserting the known
derivative boundary coefficient `dA[-3]=-2A[-2]`. -/
def rhoOne_boundaryG_terminalNegThreeRaw68
    (epsilon a a1 a0 b b3 b4 c1 c2 f f1 f2 g gm gp d2 d1 : k) : k :=
  (-(1 / 3 : k) * epsilon) * (f * (-2 * a)) +
  (-(4 / 9 : k)) *
    (f2 * g * (-2 * a) + f1 * gm * (-2 * a) + f1 * g * d2 +
      f * gp * (-2 * a) + f * gm * d2 + f * g * d1) +
  (-(2 / 27 : k)) *
    (a1 * f * (-2 * a) * (2 * c1) +
      a * f1 * (-2 * a) * (2 * c1) + a * f * d2 * (2 * c1) +
      a * f * (-2 * a) * (2 * c2)) +
  (-(1 / 9 : k) * epsilon) * (a * b * (-2 * a)) +
  (-(4 / 27 : k)) *
    (a0 * b * g * (-2 * a) + a1 * b3 * g * (-2 * a) +
      a1 * b * gm * (-2 * a) + a1 * b * g * d2 +
      a * b4 * g * (-2 * a) + a * b3 * gm * (-2 * a) +
      a * b3 * g * d2 + a * b * gp * (-2 * a) +
      a * b * gm * d2 + a * b * g * d1)

omit [IsAlgClosed k] in
/-- The genuinely new finite scalar left by terminal coefficient `-3`
after the signed-ray substitution. -/
def rhoOne_boundaryG_signedRayTerminalResidual68
    (sigma r a1 a0 b b4 c1 c2 f2 g : k) : k :=
  -2 * b ^ 2 * c1 * r ^ 7 * sigma +
    27 * b ^ 2 * g * r ^ 3 * sigma * a1 -
    81 * b * c1 * g * r ^ 2 * a1 +
    27 * b * c2 * g * r ^ 4 -
    729 * b * g ^ 2 * a0 +
    243 * b4 * g ^ 2 * r ^ 2 -
    2187 * f2 * g ^ 2

omit [IsAlgClosed k] in
/-- The terminal row is not silent on either signed ray.  The old scalar,
`I4(1)`, and terminal `-4` transport cancel both unknown derivative jets
and leave one explicit finite scalar. -/
theorem rhoOne_boundaryG_signedRay_terminalNegThree_reduce68
    (epsilon sigma r a a1 a0 b b3 b4 c1 c2 f f1 f2 g gm gp d2 d1 : k)
    (hsigma : sigma ^ 2 = 1) (hr0 : r ≠ 0) (hg : g ≠ 0)
    (hr : r ^ 2 = -3 * a)
    (hray : 27 * gm = sigma * r ^ 3 * b)
    (hrf : r * f = 3 * sigma * gm)
    (hi4one : b * gm + b3 * g + c1 * f = 0)
    (hcross : g * (3 * f1 + a1 * b) = a * b * gm)
    (hraw : rhoOne_boundaryG_terminalNegThreeRaw68 epsilon
      a a1 a0 b b3 b4 c1 c2 f f1 f2 g gm gp d2 d1 = 0) :
    rhoOne_boundaryG_signedRayTerminalResidual68
      sigma r a1 a0 b b4 c1 c2 f2 g = 0 := by
  have haeq : a = -(r ^ 2 / 3) := by
    linear_combination (1 / 3 : k) * hr
  have hgmeq : gm = sigma * r ^ 3 * b / 27 := by
    linear_combination (1 / 27 : k) * hray
  have hfeq : f = r ^ 2 * b / 9 := by
    apply (mul_left_cancel₀ hr0)
    rw [hrf, hgmeq]
    linear_combination (r ^ 3 * b / 9) * hsigma
  have hb3eq : b3 = -(b * gm + c1 * f) / g := by
    apply (eq_div_iff hg).2
    linear_combination hi4one
  have hf1eq : f1 = (a * b * gm / g - a1 * b) / 3 := by
    apply (eq_div_iff (by norm_num : (3 : k) ≠ 0)).2
    field_simp [hg]
    linear_combination hcross
  have hid :
      (59049 : k) * g *
          rhoOne_boundaryG_terminalNegThreeRaw68 epsilon
            a a1 a0 b b3 b4 c1 c2 f f1 f2 g gm gp d2 d1 =
        8 * r ^ 2 * rhoOne_boundaryG_signedRayTerminalResidual68
          sigma r a1 a0 b b4 c1 c2 f2 g := by
    rw [hb3eq, hf1eq, haeq, hgmeq, hfeq]
    dsimp only [rhoOne_boundaryG_terminalNegThreeRaw68,
      rhoOne_boundaryG_signedRayTerminalResidual68]
    field_simp [hg]
    ring
  have hz : 8 * r ^ 2 * rhoOne_boundaryG_signedRayTerminalResidual68
      sigma r a1 a0 b b4 c1 c2 f2 g = 0 := by
    rw [← hid, hraw]
    ring
  have hscale : (8 : k) * r ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
  exact (mul_eq_zero.mp hz).resolve_left hscale

/-- The signed-ray packet after consuming terminal coefficient `-3`.
The two determinant factors remain literal; the new scalar uses the same
signed square-root witness. -/
def RhoOneAlignedSquareGNegTwoSignedRayTerminal68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0) : Prop :=
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
  ∃ sigma r : k, sigma ^ 2 = 1 ∧ r ≠ 0 ∧ B.coeff 2 ≠ 0 ∧
    G.coeff (-1) ≠ 0 ∧ r ^ 2 = -3 * A.coeff (-2) ∧
    27 * G.coeff (-1) = sigma * r ^ 3 * B.coeff 2 ∧
    r * F.coeff 0 = 3 * sigma * G.coeff (-1) ∧
    (3 * C.coeff 1 + sigma * r * B.coeff 2 = 0 ∨
      -9 * Q0 + 8 * sigma * r * R0 = 0) ∧
    rhoOne_boundaryG_signedRayTerminalResidual68 sigma r
      (A.coeff (-1)) (A.coeff 0) (B.coeff 2) (B.coeff 4)
      (C.coeff 1) (C.coeff 2) (F.coeff 2) (G.coeff (-2)) = 0

/-- Source backwire for terminal coefficient `-3` on either signed ray. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_terminal68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (Q : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u)
    (Sray : RhoOneAlignedSquareGNegTwoSignedRayFactored68 T) :
    RhoOneAlignedSquareGNegTwoSignedRayTerminal68 T := by
  have Qc := Q
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68] at Qc
  rcases Qc with ⟨Rm, hquadratic⟩
  have Rmc := Rm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryMinor68] at Rmc
  rcases Rmc with ⟨Rtf, hminor⟩
  have Rtfc := Rtf
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalFollowing68] at Rtfc
  rcases Rtfc with ⟨Rt, i3two, i4three, hi3twoSrc, hi4threeSrc, hdet⟩
  have Rtc := Rt
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminalNext68] at Rtc
  rcases Rtc with ⟨Rterm, i4two, hi4twoSrc, hi4two, hprev⟩
  have Rtermc := Rterm
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryTerminal68] at Rtermc
  rcases Rtermc with ⟨Rfol, i3one, hi3oneSrc, hi3one, hprevOne⟩
  have Rfolc := Rfol
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryFollowing68] at Rfolc
  rcases Rfolc with ⟨Rn, i4one, hi4oneSrc, hi4one, hcross⟩
  have Rnc := Rn
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryNext68] at Rnc
  rcases Rnc with ⟨Rbase, hi3zero, htermFour⟩
  have Rbasec := Rbase
  dsimp only [RhoOneAlignedSquareGNegTwoBoundaryResidual68] at Rbasec
  rcases Rbasec with ⟨P, hbeta, hdelta, hzeta, hB, hC, hF, hG,
    hfneg, hgneg, hb1, hS0, hscalar, hi4base⟩
  have Sr := Sray
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayFactored68] at Sr
  rcases Sr with ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hfactorRay⟩
  obtain ⟨c, t, v, z, hc, hsingle, ht, hv, hzdef, hz, hvcore, htcore⟩ := P.1
  let A : RatFunc k := T.source.A
  let B : RatFunc k := T.source.B
  let C : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * A ^ 2
  let F : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * A * B
  let E : RatFunc k := T.source.E - RatFunc.C (1 / 27 : k) * A ^ 3
  let G : RatFunc k := E - RatFunc.C (1 / 3 : k) * A * C
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * A at hAclear
  obtain ⟨c', hc', hsingle', hderiv'⟩ :=
    ratFuncAtHahn68_linearRoot_single_deriv
      h0 T.root T.scale_degree T.root_eq
  have hcEq : c' = c := by
    have heq := congrArg (fun X : HahnSeries ℚ k => X.coeff 1)
      (hsingle'.symm.trans hsingle)
    simpa only [HahnSeries.coeff_single_same] using heq
  subst c'
  have hCmap : ratFuncAtHahn46 T.root C =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [C, A, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFmap : ratFuncAtHahn46 T.root F =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [F, A, B, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hEmap : ratFuncAtHahn46 T.root E =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [E, A, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGmap : ratFuncAtHahn46 T.root G =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [G, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hEmap, hCmap, map_mul, ratFuncAtHahn46_C]
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root A).orderTop := by simpa only [A] using P.2.1.1
  have hBH : (↑(2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root B).orderTop := by simpa only [B] using hB
  have hCH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root C).orderTop := by
    rw [hCmap]; exact hC
  have hFH : (0 : WithTop ℚ) ≤ (ratFuncAtHahn46 T.root F).orderTop := by
    rw [hFmap]; exact hF
  have hGH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root G).orderTop := by rw [hGmap]; exact hG
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (Polynomial.C x)
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hlow := constantBracket_integrated68_lowerSystem
    ratFuncDerivation68 (RatFunc.C 0) T.source.A T.source.B
      T.source.C0 T.source.D T.source.E (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.beta) (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.delta) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.zeta) (RatFunc.C T.source.eta)
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      (hconst 0) (hconst T.source.alpha) (hconst T.source.beta)
      (hconst T.source.gamma) (hconst T.source.delta)
      (hconst T.source.epsilon) (hconst T.source.zeta)
      (hconst T.source.eta) T.source.bracket_eq
  rw [hbeta, hdelta, hzeta] at hlow
  have hCrec : A ^ 2 / 3 + C = T.source.C0 := by
    dsimp only [C, A]; simp only [map_div₀, map_one, map_ofNat]; ring
  have hDrec : A * B / 3 + F = T.source.D := by
    dsimp only [F, A, B]; simp only [map_div₀, map_one, map_ofNat]; ring
  have hErec : A ^ 3 / 27 + A * C / 3 + G = T.source.E := by
    dsimp only [G, E, C, A]; simp only [map_div₀, map_one, map_ofNat]; ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) A B C F G
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR : rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
      (RatFunc.C T.source.epsilon) A B C F G
      (ratFuncDerivation68 A) (ratFuncDerivation68 B) (ratFuncDerivation68 C)
      (ratFuncDerivation68 F) (ratFuncDerivation68 G) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hdAH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv A)).orderTop := by
    dsimp only [A]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdAcoH :
      (ratFuncAtHahn46 T.root (Differential.deriv A)).coeff (-3) =
        (-2 : k) * (ratFuncAtHahn46 T.root A).coeff (-2) := by
    dsimp only [A]
    convert localHahn_deriv_coeff_neg_succ_of_cleared T.root c h0 A0
      T.source.A 2 hc hsingle hderiv' hAclear using 1 <;> norm_num
  have hdBH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv B)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root B
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBH)
  have hdCH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv C)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root C hCH
  have hdFH : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv F)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root F hFH
  have hdGH : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv G)).orderTop :=
    ratFuncAtHahn68_deriv_orderTop_ge_negThree_of_ge_negTwo
      T.root h0 G T.scale_order hGH
  let AL := ratFuncAtLaurent46 T.root A
  let BL := ratFuncAtLaurent46 T.root B
  let CL := ratFuncAtLaurent46 T.root C
  let FL := ratFuncAtLaurent46 T.root F
  let GLa := ratFuncAtLaurent46 T.root G
  let dAL := ratFuncAtLaurent46 T.root (Differential.deriv A)
  let dBL := ratFuncAtLaurent46 T.root (Differential.deriv B)
  let dCL := ratFuncAtLaurent46 T.root (Differential.deriv C)
  let dFL := ratFuncAtLaurent46 T.root (Differential.deriv F)
  let dGL := ratFuncAtLaurent46 T.root (Differential.deriv G)
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root A (-2) hAH
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root B 2 hBH
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root C 0 hCH
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root F 0 hFH
  have hGLa := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root G (-2) hGH
  have hdAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv A) (-3) hdAH
  have hdBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv B) 0 hdBH
  have hdCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv C) 0 hdCH
  have hdFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv F) 0 hdFH
  have hdGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root
    (Differential.deriv G) (-3) hdGH
  have hcs (X : RatFunc k) (n : ℤ) := ratFuncAtHahn46_coeff_int68 T.root X n
  have hdAcoL : dAL.coeff (-3) = (-2 : k) * AL.coeff (-2) := by
    rw [← hcs (Differential.deriv A) (-3), ← hcs A (-2)]
    exact hdAcoH
  have hS0L : 2 * CL.coeff 0 + 3 * T.source.gamma = 0 := by
    rw [← hcs C 0, hCmap]; exact hS0
  have hterm := rhoOneMainTangentTerminal_coeff_negThree_gNegTwo68
    T.source.gamma T.source.epsilon AL BL CL FL GLa dAL dBL dCL dFL dGL
      hAL hBL hCL hFL hGLa hdAL hdBL hdCL hdFL hdGL hS0L
  have hsparseL := congrArg (ratFuncAtLaurent46 T.root) hsparseR
  have hsparseL' : rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
      (HahnSeries.C T.source.epsilon) AL BL CL FL GLa dAL dBL dCL dFL dGL =
      ratFuncAtLaurent46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [AL, BL, CL, FL, GLa, dAL, dBL, dCL, dFL, dGL,
      rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow, map_neg,
      map_div₀, map_ofNat, map_one, ratFuncAtLaurent46_C68] using hsparseL
  have hzeroH : (ratFuncAtHahn46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-3) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [T.terminal_order]
      exact WithTop.coe_lt_coe.mpr (by norm_num))
  have hzeroL : (ratFuncAtLaurent46 T.root
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)).coeff (-3) = 0 := by
    rw [← hcs (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) (-3)]
    exact hzeroH
  have hleft := congrArg (fun X : LaurentSeries k => X.coeff (-3)) hsparseL'
  rw [hterm, hzeroL, hdAcoL] at hleft
  have hraw : rhoOne_boundaryG_terminalNegThreeRaw68 T.source.epsilon
      (AL.coeff (-2)) (AL.coeff (-1)) (AL.coeff 0)
      (BL.coeff 2) (BL.coeff 3) (BL.coeff 4)
      (CL.coeff 1) (CL.coeff 2) (FL.coeff 0) (FL.coeff 1)
      (FL.coeff 2) (GLa.coeff (-2)) (GLa.coeff (-1)) (GLa.coeff 0)
      (dAL.coeff (-2)) (dAL.coeff (-1)) = 0 := by
    dsimp only [rhoOne_boundaryG_terminalNegThreeRaw68]
    linear_combination hleft
  have htoL (X : RatFunc k) (n : ℤ) :
      (ratFuncAtLaurent46 T.root X).coeff n =
        (ratFuncAtHahn46 T.root X).coeff n := by
    rw [hcs X n]
  have hgL : GLa.coeff (-2) ≠ 0 := by
    rw [htoL G (-2), hGmap]
    exact hgneg
  have hrL : r ^ 2 = -3 * AL.coeff (-2) := by
    rw [htoL A (-2)]
    norm_num
    dsimp only [A]
    linear_combination hr
  have hrayL : 27 * GLa.coeff (-1) = sigma * r ^ 3 * BL.coeff 2 := by
    rw [htoL G (-1), htoL B 2, hGmap]
    norm_num
    simpa only [B] using hray
  have hrfL : r * FL.coeff 0 = 3 * sigma * GLa.coeff (-1) := by
    rw [htoL F 0, htoL G (-1), hFmap, hGmap]
    norm_num
    exact hrf
  have hi4L : BL.coeff 2 * GLa.coeff (-1) + BL.coeff 3 * GLa.coeff (-2) +
      CL.coeff 1 * FL.coeff 0 = 0 := by
    rw [htoL B 2, htoL G (-1), htoL B 3, htoL G (-2),
      htoL C 1, htoL F 0, hGmap, hCmap, hFmap]
    norm_num
    simpa only [B] using hi4one
  have hcrossL : GLa.coeff (-2) *
      (3 * FL.coeff 1 + AL.coeff (-1) * BL.coeff 2) =
        AL.coeff (-2) * BL.coeff 2 * GLa.coeff (-1) := by
    rw [htoL G (-2), htoL F 1, htoL A (-1),
      htoL B 2, htoL A (-2), htoL G (-1), hGmap, hFmap]
    norm_num
    simpa only [A, B, hGmap] using hcross
  have hnewL := rhoOne_boundaryG_signedRay_terminalNegThree_reduce68
    T.source.epsilon sigma r (AL.coeff (-2)) (AL.coeff (-1)) (AL.coeff 0)
    (BL.coeff 2) (BL.coeff 3) (BL.coeff 4) (CL.coeff 1) (CL.coeff 2)
    (FL.coeff 0) (FL.coeff 1) (FL.coeff 2) (GLa.coeff (-2))
    (GLa.coeff (-1)) (GLa.coeff 0) (dAL.coeff (-2)) (dAL.coeff (-1))
    hsigma hr0 hgL hrL hrayL hrfL hi4L hcrossL hraw
  have hnew := hnewL
  simp only [rhoOne_boundaryG_signedRayTerminalResidual68,
    AL, BL, CL, FL, GLa, ← hcs A (-1), ← hcs A 0, ← hcs B 2,
    ← hcs B 4, ← hcs C 1, ← hcs C 2, ← hcs F 2,
    ← hcs G (-2)] at hnew
  rw [hCmap, hFmap, hGmap] at hnew
  dsimp only [RhoOneAlignedSquareGNegTwoSignedRayTerminal68]
  refine ⟨sigma, r, hsigma, hr0, hb, hgm, hr, hray, hrf, hfactorRay, ?_⟩
  norm_num at hnew
  simp only [rhoOne_boundaryG_signedRayTerminalResidual68]
  linear_combination hnew

/-- Provenance-preserving selector: the coordinate packet (including its
new `I4(4)` row) and the nonsingular transport are unchanged. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_boundaryG_signedRay_terminal_selector68
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (R : RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u) :
    RhoOneAlignedSquareGNegTwoCoordinateGain68 T g u ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        RhoOneAlignedSquareGNegTwoSignedRayTerminal68 T) ∨
      (RhoOneAlignedSquareGNegTwoBoundaryQuadraticResidual68 T g u ∧
        let A := ratFuncAtHahn46 T.root T.source.A
        let B := ratFuncAtHahn46 T.root T.source.B
        let C := rhoOneCDefectHahn68 A (ratFuncAtHahn46 T.root T.source.C0)
        let G := rhoOneTangentEDefectHahn68 A C
          (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
        A.coeff (-2) ^ 3 * B.coeff 2 ^ 2 + 27 * G.coeff (-1) ^ 2 ≠ 0) := by
  rcases T.rhoOne_boundaryG_signedRayFactor68 R with hcoord | hsigned | hnon
  · exact Or.inl hcoord
  · exact Or.inr (Or.inl ⟨hsigned.1,
      T.rhoOne_boundaryG_signedRay_terminal68 hp hH hp6 hp5 hp4
        hsigned.1 hsigned.2⟩)
  · exact Or.inr (Or.inr hnon)

end AlignedSquareBoundaryGSignedRayTerminal68

end Max11DegreeRoutes
