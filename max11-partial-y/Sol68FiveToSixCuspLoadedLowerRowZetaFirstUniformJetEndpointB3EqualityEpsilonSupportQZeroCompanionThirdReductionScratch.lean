import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdSourceScratch

/-! # Exact reduction of the third `q=0` companion -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThirdReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Source-backed cancellation of every non-`Fce` term in the normalized
third companion. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_third_load_source68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let V:=5*N-3*S
    let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    (6:k)*((p-3:ℕ):k)^2*((p-2:ℕ):k)*((p-1:ℕ):k)*
        A.coeff (p-3)*B.coeff D^2*d.coeff V+
      (6:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
        L0.coeff (2*p-4)+
      ((p:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*A.coeff p*
        L2.coeff (p-4)+
      ((p-3:ℕ):k)*((p-1:ℕ):k)^2*A.coeff (p-1)*
        L2.coeff (p-3)+
      ((p-3:ℕ):k)*((p-2:ℕ):k)^2*A.coeff (p-2)*
        L2.coeff (p-2)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  change _=0
  have hloaded:=hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
  rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  rcases hcusp with ⟨hBtop,hctop,hdtop,hetop,hcuspEq⟩
  have hnxt:=fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq:9*N=7*S:=hnxt.1.1
  have hb0:B.coeff D≠0:=by simpa [D,hGS] using hBtop
  have hD0:A.coeff p*B.coeff D^2+3*c.coeff Cc^2=0:=by
    simpa [p,D,Cc,hGS] using hcuspEq
  have hD1:=fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD2:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD3:=fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI40:=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI41:=fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI42:=fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI43:=fiveToSix_zetaFirst_B3_equality_support_qZero_I4_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1 hD2 hD3 hI40 hI41 hI42 hI43
  have hL0:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL21:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL22:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL23:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hL0 hL21 hL22 hL23
  have halg:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_third_load_algebra68
      ((p:ℕ):k)
      (A.coeff p) (A.coeff (p-1)) (A.coeff (p-2)) (A.coeff (p-3))
      (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2)) (B.coeff (D-3))
      (c.coeff Cc) (c.coeff (Cc-1)) (c.coeff (Cc-2)) (c.coeff (Cc-3))
      (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2)) (d.coeff (V-3))
      (e.coeff E) (e.coeff (E-1)) (e.coeff (E-2)) (e.coeff (E-3))
      hb0 hD0 hD1 hD2 hD3 hI40 hI41 hI42 hI43
  have hp1:((p-1:ℕ):k)=((p:ℕ):k)-1:=by
    rw [Nat.cast_sub (by dsimp only [p];omega)];norm_num
  have hp2:((p-2:ℕ):k)=((p:ℕ):k)-2:=by
    rw [Nat.cast_sub (by dsimp only [p];omega)];norm_num
  have hp3:((p-3:ℕ):k)=((p:ℕ):k)-3:=by
    rw [Nat.cast_sub (by dsimp only [p];omega)];norm_num
  rw [hL0,hL21,hL22,hL23,hp1,hp2,hp3]
  dsimp only [p,D,Cc,V,E,FiveToSixQZeroBBDJetOne68,
    FiveToSixQZeroBBDJetTwo68] at halg ⊢
  linear_combination halg

/-- The third companion has exactly one new scalar content: the constant
compensated `I4` coefficient annihilates the cubic `A` jet. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_third_reduction68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    Fce.coeff 0*(A.coeff p*A.coeff (p-3)+
      A.coeff (p-1)*A.coeff (p-2))=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let V:=5*N-3*S
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let W0:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowZeroRemainder68
    alpha gamma epsilon zeta eta A B c d e
  let L2:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W2:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  change Fce.coeff 0*(A.coeff p*A.coeff (p-3)+
    A.coeff (p-1)*A.coeff (p-2))=0
  have hcomp:=fiveToSix_zetaFirst_B3_equality_support_qZero_companion_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hrem:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_third_cancel68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hload:=fiveToSix_zetaFirst_B3_equality_support_qZero_third_load_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionThirdScalar68]
    at hcomp
  dsimp only at hrem hload
  have hmain:(9:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
      ((2*p-3:ℕ):k)*Fce.coeff 0*
        (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2))=0:=by
    dsimp only [p,D,V,Fce,L0,W0,L2,W2]
    linear_combination hcomp-hrem-hload
  have hp3:3<p:=by
    have hloaded:=hs.1
    rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
        ⟨hGS,hGamma,hsource⟩
    have hp0:=hsource
    change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
        e.natDegree≤6*N-G-S ∧
        FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
          A B c d e N G S ∧ _ at hp0
    exact by rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
             exact by dsimp only [p];omega
  have hpm3:((p-3:ℕ):k)≠0:=by exact_mod_cast (show p-3≠0 by omega)
  have hpm2:((p-2:ℕ):k)≠0:=by exact_mod_cast (show p-2≠0 by omega)
  have hpm1:((p-1:ℕ):k)≠0:=by exact_mod_cast (show p-1≠0 by omega)
  have h2pm3:((2*p-3:ℕ):k)≠0:=by exact_mod_cast
    (show 2*p-3≠0 by omega)
  have hfac:(9:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
      ((2*p-3:ℕ):k)≠0:=by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) hpm3) hpm2) hpm1) h2pm3
  have hmul:((9:k)*((p-3:ℕ):k)*((p-2:ℕ):k)*((p-1:ℕ):k)*
      ((2*p-3:ℕ):k))*(Fce.coeff 0*
        (A.coeff p*A.coeff (p-3)+A.coeff (p-1)*A.coeff (p-2)))=0:=by
    linear_combination hmain
  exact (mul_eq_zero.mp hmul).resolve_left hfac

/-- Exact rank split through order three. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    Fce.coeff 0=0 ∨
      (A.coeff (p-1)=0 ∧ A.coeff (p-2)=0 ∧ A.coeff (p-3)=0):=by
  let p:=2*N
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  change Fce.coeff 0=0 ∨
    (A.coeff (p-1)=0 ∧ A.coeff (p-2)=0 ∧ A.coeff (p-3)=0)
  by_cases hf:Fce.coeff 0=0
  · exact Or.inl hf
  · right
    have hprev:=
      fiveToSix_zetaFirst_B3_equality_support_qZero_second_companion_split68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    have hthird:=
      fiveToSix_zetaFirst_B3_equality_support_qZero_companion_third_reduction68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only at hprev hthird
    rcases hprev with hf0|⟨ha1,ha2⟩
    · exact (hf hf0).elim
    have hjet:A.coeff p*A.coeff (p-3)+
        A.coeff (p-1)*A.coeff (p-2)=0:=
      (mul_eq_zero.mp (by simpa only [p,Fce] using hthird)).resolve_left hf
    have hloaded:=hs.1
    rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
        ⟨hGS,hGamma,hsource⟩
    have hp0:=hsource
    change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
        e.natDegree≤6*N-G-S ∧
        FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
          A B c d e N G S ∧ _ at hp0
    rcases hp0 with ⟨hS,hSR,hd,he,hpacket,hrest⟩
    rcases hpacket with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
    have ha0:A.coeff p≠0:=by simpa [p] using hatop
    have ha3:A.coeff (p-3)=0:=by
      apply (mul_left_cancel₀ ha0)
      rw [ha1,ha2] at hjet
      linear_combination hjet
    exact ⟨ha1,ha2,ha3⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_third_load_source68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_third_reduction68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_third_companion_split68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionThirdReduction68

end Max11DegreeRoutes
