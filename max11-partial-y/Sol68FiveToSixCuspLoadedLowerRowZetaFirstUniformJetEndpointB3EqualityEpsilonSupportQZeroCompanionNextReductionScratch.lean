import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadNextScratch

/-! # Exact reduction of the second `q=0` companion -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionNextReduction68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The load part of the second companion is in the localized ideal generated
by discriminant and `I4` jets through order two.  The localization is honest:
the source packet makes the leading `B` coefficient nonzero. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_second_load_algebra68
    (P a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2 e0 e1 e2:k)
    (hb0:b0≠0)
    (hD0:a0*b0^2+3*c0^2=0)
    (hD1:a1*b0^2+2*a0*b0*b1+6*c0*c1=0)
    (hD2:a2*b0^2+2*a1*b0*b1+a0*(2*b0*b2+b1^2)+
      3*(2*c0*c2+c1^2)=0)
    (hI40:b0*e0+c0*d0=0)
    (hI41:b1*e0+b0*e1+c1*d0+c0*d1=0)
    (hI42:b2*e0+b1*e1+b0*e2+c2*d0+c1*d1+c0*d2=0):
    (P-2)*a2*b0^2*d0+
      (P-1)*a1*(b0^2*d1+2*b0*b1*d0)+
      ((11/14:k)*P)*a2*b0^2*d0+
      ((11/7:k)*P-1)*a1*b0*b1*d0+
      ((11/14:k)*P-1)*a1*b0^2*d1+
      2*((11/14:k)*P-1)*a0*b0*b2*d0+
      ((11/14:k)*P-1)*a0*b1^2*d0+
      ((11/7:k)*P-3)*a0*b0*b1*d1+
      ((11/14:k)*P-2)*a0*b0^2*d2-
      3*((15/14:k)*P*b2*c0*e0+
        (15/14:k)*P*b1*c1*e0+((15/14:k)*P-1)*b1*c0*e1+
        (15/14:k)*P*b0*c2*e0+((15/14:k)*P-1)*b0*c1*e1+
        ((15/14:k)*P-2)*b0*c0*e2)+
      3*(((10/7:k)*P-2)*c0*c2*d0+
        ((5/7:k)*P-1)*c1^2*d0+
        ((10/7:k)*P-1)*c0*c1*d1+(5/7:k)*P*c0^2*d2)+
      P*a0*(b0^2*d2+2*b0*b1*d1+2*b0*b2*d0+b1^2*d0)=0:=by
  have hmul:b0^2*((P-2)*a2*b0^2*d0+
      (P-1)*a1*(b0^2*d1+2*b0*b1*d0)+
      ((11/14:k)*P)*a2*b0^2*d0+
      ((11/7:k)*P-1)*a1*b0*b1*d0+
      ((11/14:k)*P-1)*a1*b0^2*d1+
      2*((11/14:k)*P-1)*a0*b0*b2*d0+
      ((11/14:k)*P-1)*a0*b1^2*d0+
      ((11/7:k)*P-3)*a0*b0*b1*d1+
      ((11/14:k)*P-2)*a0*b0^2*d2-
      3*((15/14:k)*P*b2*c0*e0+
        (15/14:k)*P*b1*c1*e0+((15/14:k)*P-1)*b1*c0*e1+
        (15/14:k)*P*b0*c2*e0+((15/14:k)*P-1)*b0*c1*e1+
        ((15/14:k)*P-2)*b0*c0*e2)+
      3*(((10/7:k)*P-2)*c0*c2*d0+
        ((5/7:k)*P-1)*c1^2*d0+
        ((10/7:k)*P-1)*c0*c1*d1+(5/7:k)*P*c0^2*d2)+
      P*a0*(b0^2*d2+2*b0*b1*d1+2*b0*b2*d0+b1^2*d0))=0:=by
    linear_combination
      (-b1^2*d0+2*b0*b2*d0+b0*b1*d1+
          ((25:k)*P-28)/14*b0^2*d2)*hD0+
      (b0*b1*d0+((25:k)*P-28)/14*b0^2*d1)*hD1+
      (((25:k)*P-28)/14*b0^2*d0)*hD2+
      (3*b1^2*c0-6*b0*b2*c0-3*b0*b1*c1-
          ((45:k)*P)/14*b0^2*c2)*hI40+
      (-3*b0*b1*c0+(-(45:k)*P+42)/14*b0^2*c1)*hI41+
      ((-(45:k)*P+84)/14*b0^2*c0)*hI42
  have hb02:b0^2≠0:=pow_ne_zero 2 hb0
  exact (mul_eq_zero.mp hmul).resolve_left hb02

/-- Source-backed cancellation of every non-`Fce` term in the normalized
second companion. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_second_load_source68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let V:=5*N-3*S
    let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    (((p-2:ℕ):k)*A.coeff (p-2)*B.coeff D^2*d.coeff V+
      ((p-1:ℕ):k)*A.coeff (p-1)*
        (B.coeff D^2*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V)+
      L0.coeff (2*p-3)+
      ((p:ℕ):k)*A.coeff p*
        (B.coeff D^2*d.coeff (V-2)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-2)*d.coeff V+
          B.coeff (D-1)^2*d.coeff V))=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let L0:=FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  change (((p-2:ℕ):k)*A.coeff (p-2)*B.coeff D^2*d.coeff V+
      ((p-1:ℕ):k)*A.coeff (p-1)*
        (B.coeff D^2*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff V)+
      L0.coeff (2*p-3)+
      ((p:ℕ):k)*A.coeff p*
        (B.coeff D^2*d.coeff (V-2)+
          (2:k)*B.coeff D*B.coeff (D-1)*d.coeff (V-1)+
          (2:k)*B.coeff D*B.coeff (D-2)*d.coeff V+
          B.coeff (D-1)^2*d.coeff V))=0
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
  have hb0:B.coeff D≠0:=by simpa [D,hGS] using hBtop
  have hD0:A.coeff p*B.coeff D^2+3*c.coeff Cc^2=0:=by
    simpa [p,D,Cc,hGS] using hcuspEq
  have hD1:=fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD2:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI40:=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI41:=fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI42:=fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1 hD2 hI40 hI41 hI42
  have hL0:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hL0
  have hsupport:=hs.1.1
  rcases hsupport with ⟨hstop,hTD⟩
  have hEq:9*N=7*S:=by dsimp only at hTD;omega
  have hVDnat:14*(V+D)=11*p:=by dsimp only [p,D,V];omega
  have hEnat:14*E=15*p:=by dsimp only [p,E];omega
  have hCnat:7*Cc=5*p:=by dsimp only [p,Cc];omega
  have hVD:((V:ℕ):k)+((D:ℕ):k)=(11/14:k)*((p:ℕ):k):=by
    have h:=congrArg (fun n:ℕ=>(n:k)) hVDnat
    push_cast at h
    linear_combination h/14
  have hEc:((E:ℕ):k)=(15/14:k)*((p:ℕ):k):=by
    have h:=congrArg (fun n:ℕ=>(n:k)) hEnat
    push_cast at h
    linear_combination h/14
  have hCc:((Cc:ℕ):k)=(5/7:k)*((p:ℕ):k):=by
    have h:=congrArg (fun n:ℕ=>(n:k)) hCnat
    push_cast at h
    linear_combination h/7
  have h2VD:(2:k)*((V:ℕ):k)+(2:k)*((D:ℕ):k)=
      (11/7:k)*((p:ℕ):k):=by
    linear_combination 2*hVD
  have h2Cc:(2:k)*((Cc:ℕ):k)=(10/7:k)*((p:ℕ):k):=by
    linear_combination 2*hCc
  have hp2:2≤p:=by dsimp only [p];omega
  have hpcast2:((p-2:ℕ):k)=((p:ℕ):k)-2:=by
    rw [Nat.cast_sub hp2]
    norm_num
  have hpcast1:((p-1:ℕ):k)=((p:ℕ):k)-1:=by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have halg:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_second_load_algebra68
      ((p:ℕ):k)
      (A.coeff p) (A.coeff (p-1)) (A.coeff (p-2))
      (B.coeff D) (B.coeff (D-1)) (B.coeff (D-2))
      (c.coeff Cc) (c.coeff (Cc-1)) (c.coeff (Cc-2))
      (d.coeff V) (d.coeff (V-1)) (d.coeff (V-2))
      (e.coeff E) (e.coeff (E-1)) (e.coeff (E-2))
      hb0 hD0 hD1 hD2 hI40 hI41 hI42
  rw [hL0]
  rw [h2VD,h2Cc,hVD,hEc,hCc,hpcast2,hpcast1]
  linear_combination halg

/-- The exact second companion has one new scalar content: the constant
compensated `I4` coefficient annihilates the quadratic `A` second jet. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_companion_next_reduction68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    Fce.coeff 0*((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2)=0:=by
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
  change Fce.coeff 0*
    ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2)=0
  have hcomp:=fiveToSix_zetaFirst_B3_equality_support_qZero_companion_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hrem:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_remainder_next_cancel68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hload:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_second_load_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL2old:=fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL2new:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroCompanionNextScalar68]
    at hcomp
  dsimp only at hrem hload hL2old hL2new
  have hmain:(9:k)*((p-2:ℕ):k)*((p-1:ℕ):k)*Fce.coeff 0*
      ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2)=0:=by
    dsimp only [p,D,V,Fce,L0,W0,L2,W2]
    rw [hL2old,hL2new] at hcomp
    linear_combination hcomp-(6:k)*(((2*N-2:ℕ):k))*hload-hrem
  have hp2:2<p:=by
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
    exact by dsimp only [p];omega
  have hp2cast:(((p-2:ℕ):k))≠0:=by
    exact_mod_cast (show p-2≠0 by omega)
  have hp1cast:(((p-1:ℕ):k))≠0:=by
    exact_mod_cast (show p-1≠0 by omega)
  have hfactor:(9:k)*((p-2:ℕ):k)*((p-1:ℕ):k)≠0:=
    mul_ne_zero (mul_ne_zero (by norm_num) hp2cast) hp1cast
  have hmain':((9:k)*((p-2:ℕ):k)*((p-1:ℕ):k))*
      (Fce.coeff 0*
        ((2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2))=0:=by
    linear_combination hmain
  exact (mul_eq_zero.mp hmain').resolve_left hfactor

/-- Exact rank split through second order.  On the nonzero constant-`I4`
branch the two companion rows kill `A_(p-1)` and `A_(p-2)`; on the zero
branch neither companion adds rank. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_second_companion_split68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    Fce.coeff 0=0 ∨
      (A.coeff (p-1)=0 ∧ A.coeff (p-2)=0):=by
  let p:=2*N
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  change Fce.coeff 0=0 ∨
    (A.coeff (p-1)=0 ∧ A.coeff (p-2)=0)
  by_cases hf:Fce.coeff 0=0
  · exact Or.inl hf
  · right
    have hfirst:=fiveToSix_zetaFirst_B3_equality_support_qZero_jet_rank68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    have hsecond:=
      fiveToSix_zetaFirst_B3_equality_support_qZero_companion_next_reduction68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only at hfirst hsecond
    have ha1:A.coeff (p-1)=0:=
      (mul_eq_zero.mp (by simpa only [p,Fce] using hfirst)).resolve_left hf
    have hquad:(2:k)*A.coeff p*A.coeff (p-2)+A.coeff (p-1)^2=0:=
      (mul_eq_zero.mp (by simpa only [p,Fce] using hsecond)).resolve_left hf
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
    have htwoa0:(2:k)*A.coeff p≠0:=mul_ne_zero (by norm_num) ha0
    refine ⟨ha1,?_⟩
    apply (mul_left_cancel₀ htwoa0)
    rw [ha1] at hquad
    linear_combination hquad

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_second_load_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_second_load_source68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_companion_next_reduction68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_second_companion_split68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroCompanionNextReduction68

end Max11DegreeRoutes
