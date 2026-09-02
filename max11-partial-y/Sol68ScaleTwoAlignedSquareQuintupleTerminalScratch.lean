import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDoubleZeroQuintupleGainNext

/-! # The unused terminal row at the aligned-square quintuple box -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareQuintupleTerminal68

variable {k : Type*} [Field k] [CharZero k]

local instance alignedSquareQuintupleTerminalHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- The sparse terminal one-form left after the rho-one main-tangent
substitution.  Notice that the ground constants `alpha` and `eta` cancel. -/
def rhoOneMainTangentTerminal68 {F : Type*} [Field F]
    (gamma epsilon A B C F0 G dA dB dC dF dG : F) : F :=
  (-2 / 3 * gamma) * F0 * dC +
  (-1 / 3 * epsilon) * F0 * dA +
  (-4 / 9) * F0 * G * dA +
  (-4 / 9) * F0 * F0 * dB +
  (-4 / 9) * C * F0 * dC +
  (2 / 3 * gamma) * B * dG +
  (-4 / 9) * B * F0 * dF +
  (4 / 9) * B * C * dG +
  (2 / 9 * gamma) * B * C * dA +
  (4 / 27) * B * C * C * dA +
  (-2 / 9 * gamma) * A * F0 * dA +
  (-4 / 27) * A * C * F0 * dA +
  (-1 / 9 * epsilon) * A * B * dA +
  (-4 / 27) * A * B * G * dA +
  (-4 / 27) * A * B * F0 * dB +
  (-4 / 27) * A * B * B * dF

set_option maxHeartbeats 3000000 in
/-- Exact factorization of the last integrated Jacobian row on the main
tangent, with `L=beta=delta=zeta=0`. -/
theorem integratedTerminal_mainTangent_factorization68
    {F : Type*} [Field F] [CharZero F] [Algebra k F]
    (d : Derivation k F F)
    (alpha gamma epsilon eta A B C F0 G : F)
    (halpha : d alpha = 0) (hgamma : d gamma = 0)
    (hepsilon : d epsilon = 0) (heta : d eta = 0) :
    integratedU68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F0)
        (A ^ 3 / 27 + A * C / 3 + G) alpha 0 gamma 0 0 *
          d (A ^ 3 / 27 + A * C / 3 + G) -
      (A * B / 3 + F0) *
        d (integratedV68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F0)
          (A ^ 3 / 27 + A * C / 3 + G) alpha 0 gamma 0 epsilon eta) =
      rhoOneMainTangentTerminal68 gamma epsilon A B C F0 G
        (d A) (d B) (d C) (d F0) (d G) := by
  have h1 : d (1 : F) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  simp only [integratedU68, integratedV68, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
    Derivation.leibniz_inv, nsmul_eq_mul, smul_eq_mul, halpha, hgamma,
    hepsilon, heta, map_zero, zero_mul, mul_zero, add_zero, sub_zero]
  simp [derivation_ofNat_zero68 d, h1]
  simp only [rhoOneMainTangentTerminal68]
  ring

set_option maxHeartbeats 3000000 in
/-- Every term of the sparse terminal row is regular in the fifth-gain
box.  This is deliberately stated independently of the source wrapper. -/
theorem rhoOneMainTangentTerminal_orderTop_nonneg68
    (gamma epsilon : k)
    (A B C F0 G dA dB dC dF dG : HahnSeries ℚ k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(5 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (0 : WithTop ℚ) ≤ C.orderTop)
    (hF : (↑(5 : ℚ) : WithTop ℚ) ≤ F0.orderTop)
    (hG : (0 : WithTop ℚ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℚ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℚ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℚ) ≤ dF.orderTop)
    (hdG : (0 : WithTop ℚ) ≤ dG.orderTop) :
    (0 : WithTop ℚ) ≤
      (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F0 G dA dB dC dF dG).orderTop := by
  have hposDiv (m n : ℕ) : (0 : WithTop ℚ) ≤
      (((m : HahnSeries ℚ k) / (n : HahnSeries ℚ k))).orderTop :=
    hahnOrderTop_natDiv_nonneg46 m n
  have hnegDiv (m n : ℕ) : (0 : WithTop ℚ) ≤
      ((-(m : HahnSeries ℚ k) / (n : HahnSeries ℚ k))).orderTop := by
    rw [neg_div]
    exact hahnOrderTop_neg_nonneg46 _ (hposDiv m n)
  have hm2 : (0 : WithTop ℚ) ≤
      ((-2 / 3 : HahnSeries ℚ k) * HahnSeries.C gamma).orderTop :=
    hahnOrderTop_mul_nonneg46 _ _ (hnegDiv 2 3)
      (hahnOrderTop_C_nonneg46 _)
  have hneg13 : (0 : WithTop ℚ) ≤
      ((-1 / 3 : HahnSeries ℚ k)).orderTop := by
    convert hnegDiv 1 3 using 1 <;> norm_num
  have hm1e : (0 : WithTop ℚ) ≤
      ((-1 / 3 : HahnSeries ℚ k) * HahnSeries.C epsilon).orderTop :=
    hahnOrderTop_mul_nonneg46 _ _ hneg13
      (hahnOrderTop_C_nonneg46 _)
  have hp2 : (0 : WithTop ℚ) ≤
      ((2 / 3 : HahnSeries ℚ k) * HahnSeries.C gamma).orderTop :=
    hahnOrderTop_mul_nonneg46 _ _ (hposDiv 2 3)
      (hahnOrderTop_C_nonneg46 _)
  have hp29 : (0 : WithTop ℚ) ≤
      ((2 / 9 : HahnSeries ℚ k) * HahnSeries.C gamma).orderTop :=
    hahnOrderTop_mul_nonneg46 _ _ (hposDiv 2 9)
      (hahnOrderTop_C_nonneg46 _)
  have hm29 : (0 : WithTop ℚ) ≤
      ((-2 / 9 : HahnSeries ℚ k) * HahnSeries.C gamma).orderTop :=
    hahnOrderTop_mul_nonneg46 _ _ (hnegDiv 2 9)
      (hahnOrderTop_C_nonneg46 _)
  have hneg19 : (0 : WithTop ℚ) ≤
      ((-1 / 9 : HahnSeries ℚ k)).orderTop := by
    convert hnegDiv 1 9 using 1 <;> norm_num
  have hm19e : (0 : WithTop ℚ) ≤
      ((-1 / 9 : HahnSeries ℚ k) * HahnSeries.C epsilon).orderTop :=
    hahnOrderTop_mul_nonneg46 _ _ hneg19
      (hahnOrderTop_C_nonneg46 _)
  have mul2 (S X Y : HahnSeries ℚ k) (rX rY : ℚ)
      (hS : (0 : WithTop ℚ) ≤ S.orderTop)
      (hX : (↑rX : WithTop ℚ) ≤ X.orderTop)
      (hY : (↑rY : WithTop ℚ) ≤ Y.orderTop)
      (hsum : 0 ≤ rX + rY) :
      (0 : WithTop ℚ) ≤ (S * X * Y).orderTop := by
    have hSX := hahnOrderTop_mul_lower46 S X 0 rX hS hX
    have hSXY := hahnOrderTop_mul_lower46 (S * X) Y (0 + rX) rY hSX hY
    exact (WithTop.coe_le_coe.mpr (by simpa using hsum)).trans
      (by simpa only [zero_add] using hSXY)
  have mul3 (S X Y Z : HahnSeries ℚ k) (rX rY rZ : ℚ)
      (hS : (0 : WithTop ℚ) ≤ S.orderTop)
      (hX : (↑rX : WithTop ℚ) ≤ X.orderTop)
      (hY : (↑rY : WithTop ℚ) ≤ Y.orderTop)
      (hZ : (↑rZ : WithTop ℚ) ≤ Z.orderTop)
      (hsum : 0 ≤ rX + rY + rZ) :
      (0 : WithTop ℚ) ≤ (S * X * Y * Z).orderTop := by
    have hSX := hahnOrderTop_mul_lower46 S X 0 rX hS hX
    have hSXY := hahnOrderTop_mul_lower46 (S * X) Y (0 + rX) rY hSX hY
    have hSXYZ := hahnOrderTop_mul_lower46 (S * X * Y) Z
      (0 + rX + rY) rZ hSXY hZ
    exact (WithTop.coe_le_coe.mpr (by simpa using hsum)).trans
      (by simpa only [zero_add] using hSXYZ)
  have mul4 (S X Y Z W : HahnSeries ℚ k) (rX rY rZ rW : ℚ)
      (hS : (0 : WithTop ℚ) ≤ S.orderTop)
      (hX : (↑rX : WithTop ℚ) ≤ X.orderTop)
      (hY : (↑rY : WithTop ℚ) ≤ Y.orderTop)
      (hZ : (↑rZ : WithTop ℚ) ≤ Z.orderTop)
      (hW : (↑rW : WithTop ℚ) ≤ W.orderTop)
      (hsum : 0 ≤ rX + rY + rZ + rW) :
      (0 : WithTop ℚ) ≤ (S * X * Y * Z * W).orderTop := by
    have hSX := hahnOrderTop_mul_lower46 S X 0 rX hS hX
    have hSXY := hahnOrderTop_mul_lower46 (S * X) Y (0 + rX) rY hSX hY
    have hSXYZ := hahnOrderTop_mul_lower46 (S * X * Y) Z
      (0 + rX + rY) rZ hSXY hZ
    have hSXYZW := hahnOrderTop_mul_lower46 (S * X * Y * Z) W
      (0 + rX + rY + rZ) rW hSXYZ hW
    exact (WithTop.coe_le_coe.mpr (by simpa using hsum)).trans
      (by simpa only [zero_add] using hSXYZW)
  have t1 := mul2 ((-2 / 3 : HahnSeries ℚ k) * HahnSeries.C gamma)
    F0 dC 5 0 hm2 hF hdC (by norm_num)
  have t2 := mul2 ((-1 / 3 : HahnSeries ℚ k) * HahnSeries.C epsilon)
    F0 dA 5 (-3) hm1e hF hdA (by norm_num)
  have t3 := mul3 (-4 / 9 : HahnSeries ℚ k) F0 G dA
    5 0 (-3) (hnegDiv 4 9) hF hG hdA
      (by norm_num)
  have t4 := mul3 (-4 / 9 : HahnSeries ℚ k) F0 F0 dB
    5 5 0 (hnegDiv 4 9) hF hF hdB
      (by norm_num)
  have t5 := mul3 (-4 / 9 : HahnSeries ℚ k) C F0 dC
    0 5 0 (hnegDiv 4 9) hC hF hdC
      (by norm_num)
  have t6 := mul2 ((2 / 3 : HahnSeries ℚ k) * HahnSeries.C gamma)
    B dG 5 0 hp2 hB hdG (by norm_num)
  have t7 := mul3 (-4 / 9 : HahnSeries ℚ k) B F0 dF
    5 5 0 (hnegDiv 4 9) hB hF hdF
      (by norm_num)
  have t8 := mul3 (4 / 9 : HahnSeries ℚ k) B C dG
    5 0 0 (hposDiv 4 9) hB hC hdG
      (by norm_num)
  have t9 := mul3 ((2 / 9 : HahnSeries ℚ k) * HahnSeries.C gamma)
    B C dA 5 0 (-3) hp29 hB hC hdA (by norm_num)
  have t10 := mul4 (4 / 27 : HahnSeries ℚ k) B C C dA
    5 0 0 (-3) (hposDiv 4 27) hB hC hC hdA
      (by norm_num)
  have t11 := mul3 ((-2 / 9 : HahnSeries ℚ k) * HahnSeries.C gamma)
    A F0 dA (-2) 5 (-3) hm29 hA hF hdA (by norm_num)
  have t12 := mul4 (-4 / 27 : HahnSeries ℚ k) A C F0 dA
    (-2) 0 5 (-3) (hnegDiv 4 27) hA hC hF hdA
      (by norm_num)
  have t13 := mul3 ((-1 / 9 : HahnSeries ℚ k) * HahnSeries.C epsilon)
    A B dA (-2) 5 (-3) hm19e hA hB hdA (by norm_num)
  have t14 := mul4 (-4 / 27 : HahnSeries ℚ k) A B G dA
    (-2) 5 0 (-3) (hnegDiv 4 27) hA hB hG hdA
      (by norm_num)
  have t15 := mul4 (-4 / 27 : HahnSeries ℚ k) A B F0 dB
    (-2) 5 5 0 (hnegDiv 4 27) hA hB hF hdB
      (by norm_num)
  have t16 := mul4 (-4 / 27 : HahnSeries ℚ k) A B B dF
    (-2) 5 5 0 (hnegDiv 4 27) hA hB hB hdF
      (by norm_num)
  have s2 := hahnOrderTop_add_nonneg46 _ _ t1 t2
  have s3 := hahnOrderTop_add_nonneg46 _ _ s2 t3
  have s4 := hahnOrderTop_add_nonneg46 _ _ s3 t4
  have s5 := hahnOrderTop_add_nonneg46 _ _ s4 t5
  have s6 := hahnOrderTop_add_nonneg46 _ _ s5 t6
  have s7 := hahnOrderTop_add_nonneg46 _ _ s6 t7
  have s8 := hahnOrderTop_add_nonneg46 _ _ s7 t8
  have s9 := hahnOrderTop_add_nonneg46 _ _ s8 t9
  have s10 := hahnOrderTop_add_nonneg46 _ _ s9 t10
  have s11 := hahnOrderTop_add_nonneg46 _ _ s10 t11
  have s12 := hahnOrderTop_add_nonneg46 _ _ s11 t12
  have s13 := hahnOrderTop_add_nonneg46 _ _ s12 t13
  have s14 := hahnOrderTop_add_nonneg46 _ _ s13 t14
  have s15 := hahnOrderTop_add_nonneg46 _ _ s14 t15
  have s16 := hahnOrderTop_add_nonneg46 _ _ s15 t16
  exact s16

/-- The direct terminal Keller row excludes the entire fifth-gain box. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_quintupleBox_impossible
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB :
      (↑(5 : ℚ) : WithTop ℚ) ≤
        (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC :
      (0 : WithTop ℚ) ≤
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF :
      (↑(5 : ℚ) : WithTop ℚ) ≤
        (rhoOneTangentDDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.B)
          (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG :
      (0 : WithTop ℚ) ≤
        (rhoOneTangentEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (rhoOneCDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.C0))
          (rhoOneEDefectHahn68
            (ratFuncAtHahn46 T.root T.source.A)
            (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) : False := by
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ER : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ER - RatFunc.C (1 / 3 : k) * AR * CR
  let A0 := localClearedA68RhoOne g u
  have hAclear := (T.source.clearedCoordinatesRhoOne hp T.scale_ne_zero
    hH hp6 hp5 hp4).1
  change algebraMap k[X] (RatFunc k) A0 =
    (algebraMap k[X] (RatFunc k) h0) ^ 2 * AR at hAclear
  have hconst (x : k) : ratFuncDerivation68 (RatFunc.C x) = 0 := by
    have hx := GCD369RatFuncDerivative (C x : k[X])
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
  have hCrec : AR ^ 2 / 3 + CR = C0R := by
    dsimp only [CR, AR, C0R]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hDrec : AR * BR / 3 + FR = DR := by
    dsimp only [FR, AR, BR, DR]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hErec : AR ^ 3 / 27 + AR * CR / 3 + GR = E0R := by
    dsimp only [GR, ER, CR, AR, C0R, E0R]
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hfactor := integratedTerminal_mainTangent_factorization68
    ratFuncDerivation68 (RatFunc.C T.source.alpha)
      (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
      (RatFunc.C T.source.eta) AR BR CR FR GR
      (hconst T.source.alpha) (hconst T.source.gamma)
      (hconst T.source.epsilon) (hconst T.source.eta)
  have hsparseR :
      rhoOneMainTangentTerminal68 (RatFunc.C T.source.gamma)
        (RatFunc.C T.source.epsilon) AR BR CR FR GR
        (ratFuncDerivation68 AR) (ratFuncDerivation68 BR)
        (ratFuncDerivation68 CR) (ratFuncDerivation68 FR)
        (ratFuncDerivation68 GR) =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0 := by
    rw [← hfactor, hCrec, hDrec, hErec]
    simpa only [map_zero] using hlow.2.2.2.2
  have hsparseH := congrArg (ratFuncAtHahn46 T.root) hsparseR
  have hsparseH' :
      rhoOneMainTangentTerminal68 (HahnSeries.C T.source.gamma)
        (HahnSeries.C T.source.epsilon)
        (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
        (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
        (ratFuncAtHahn46 T.root GR)
        (ratFuncAtHahn46 T.root (Differential.deriv AR))
        (ratFuncAtHahn46 T.root (Differential.deriv BR))
        (ratFuncAtHahn46 T.root (Differential.deriv CR))
        (ratFuncAtHahn46 T.root (Differential.deriv FR))
        (ratFuncAtHahn46 T.root (Differential.deriv GR)) =
      ratFuncAtHahn46 T.root
        (RatFunc.C j / algebraMap k[X] (RatFunc k) h0) := by
    simpa only [rhoOneMainTangentTerminal68, ratFuncDerivation68,
      ratFuncDerivation46_apply, map_add, map_mul, map_pow,
      ratFuncAtHahn46_C, map_div₀, map_neg, map_ofNat, map_one]
      using hsparseH
  have hbounds := P.2.1
  dsimp only [RhoOneZeroLCubicImprovedHahnBounds68] at hbounds
  have hAH : (↑(-2 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root AR).orderTop := by
    simpa only [AR] using hbounds.1
  have hCRmap : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [CR, C0R, AR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [FR, DR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ER =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [ER, E0R, AR, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hGRmap : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68
          (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    dsimp only [GR, rhoOneTangentEDefectHahn68]
    rw [map_sub, map_mul, hERmap, hCRmap]
    rw [map_mul, ratFuncAtHahn46_C]
  have hBR : (↑(5 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root BR).orderTop := by simpa only [BR] using hB
  have hCR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root CR).orderTop := by rw [hCRmap]; exact hC
  have hFR : (↑(5 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root FR).orderTop := by rw [hFRmap]; exact hF
  have hGR : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root GR).orderTop := by rw [hGRmap]; exact hG
  have hdA : (↑(-3 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv AR)).orderTop := by
    dsimp only [AR]
    convert localHahn_deriv_orderTop_ge_of_cleared T.root h0 A0
      T.source.A 2 T.scale_order hAclear using 1 <;> norm_num
  have hdB : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv BR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root BR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hBR)
  have hdC : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv CR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root CR hCR
  have hdF : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv FR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root FR
      (le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hFR)
  have hdG : (0 : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root (Differential.deriv GR)).orderTop :=
    ratFuncAtHahn46_deriv_orderTop_nonneg_of_nonneg T.root GR hGR
  have hregular := rhoOneMainTangentTerminal_orderTop_nonneg68
    T.source.gamma T.source.epsilon
      (ratFuncAtHahn46 T.root AR) (ratFuncAtHahn46 T.root BR)
      (ratFuncAtHahn46 T.root CR) (ratFuncAtHahn46 T.root FR)
      (ratFuncAtHahn46 T.root GR)
      (ratFuncAtHahn46 T.root (Differential.deriv AR))
      (ratFuncAtHahn46 T.root (Differential.deriv BR))
      (ratFuncAtHahn46 T.root (Differential.deriv CR))
      (ratFuncAtHahn46 T.root (Differential.deriv FR))
      (ratFuncAtHahn46 T.root (Differential.deriv GR))
      hAH hBR hCR hFR hGR hdA hdB hdC hdF hdG
  rw [hsparseH', T.terminal_order] at hregular
  exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℚ) < 0)))
    hregular

end AlignedSquareQuintupleTerminal68

end Max11DegreeRoutes
