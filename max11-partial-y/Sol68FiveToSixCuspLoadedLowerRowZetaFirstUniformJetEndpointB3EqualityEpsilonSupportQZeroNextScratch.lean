import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportLeadingScratch

/-! # The exact `q=0` support coincidence and its first lower coefficient

The support inequality turns `9*N-7*S=0` into the genuine equality
`9*N=7*S`, equivalently `D=T`.  At that wall the compensated I4 is
constant and the compensated I3 has support at most `2*D`.  We then retain
the literal next row-two coefficient.  Its `J_(p-1)` transport slope is
nonzero; every other one-lower source term is kept in a named remainder.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroNext68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The complete literal row two from the frozen source packet. -/
def FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X]):k[X]:=
  secondaryResidualRowTwoPolynomial68 A B c d e+
    cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1/3:k)•(A*B)+d) e

/-- All terms below the already-factored support block.  Defining this as
the literal difference makes every load coincidence at the next index
explicitly source-preserving rather than silently discarded. -/
def FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X]):k[X]:=
  FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
      alpha gamma epsilon zeta eta A B c d e-
    (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
      (9*gamma:k)•(A*derivative d)+
      (9/2*gamma:k)•(d*derivative A)+
      (9/4*epsilon:k)•(derivative A*B)-
      (9/2*epsilon:k)•(A*derivative B)+
      FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d)

def FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68
    (alpha gamma epsilon zeta eta:k) (A B c d e:k[X])
    (N S:ℕ):Prop:=
  let D:=3*N-2*S
  let p:=11*N-7*S
  let idx:=p-2
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rce:=R+(9/2*gamma:k)•e+(9/4*epsilon:k)•c
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  (9*N=7*S ∧ S-2*D=D) ∧
    (∃ i4 i3:k,
      Fce=(3/8:k)•C i4 ∧
      Rce=(3/4*gamma:k)•B^2+(9/8:k)•C i3 ∧
      Rce.natDegree≤2*D) ∧
    (((p-1:ℕ):k)*
        ((3:k)*A.coeff (p-1)*Fce.coeff 0+
          (6:k)*J.coeff (p-1))+L.coeff idx+W.coeff idx=0) ∧
      (((p-1:ℕ):k))≠0

/-- Exact same-source extraction on the coincident support wall.  The final
equation is the first coefficient below the retained support row; its
nonzero slope proves that it is an honest `J_(p-1)` transport equation. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68
      alpha gamma epsilon zeta eta A B c d e N S:=by
  let D:=3*N-2*S
  let p:=11*N-7*S
  let idx:=p-2
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  let R:=(-(A*B*d)+(3:k)•(c*e))-B^2*c+(3/2:k)•d^2
  let Rce:=R+(9/2*gamma:k)•e+(9/4*epsilon:k)•c
  let J:=(B*c^2-(1/9:k)•(A*B^3))-(3:k)•(d*e)
  let L:=FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let W:=FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68
    alpha gamma epsilon zeta eta A B c d e
  have hloaded:=hs.1
  rcases hloaded with ⟨hsupport,hrows⟩
  rcases hsupport with ⟨hstop,hTD⟩
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S
      ⟨⟨hstop,hTD⟩,hrows⟩ with ⟨hGS,hGamma,hsource⟩
  have hp0:=hsource
  change 0<S ∧ S<7*N-2*G ∧ d.natDegree≤5*N-G-S ∧
      e.natDegree≤6*N-G-S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS,hSR,hd,he,hp0,hrest⟩
  rcases hp0 with ⟨hN,hgt,hle,hA,hB,hc,hd0,he0,hatop,hcusp,had⟩
  have hEq:9*N=7*S:=by
    dsimp only [D] at hTD
    omega
  have hDT:S-2*D=D:=by dsimp only [D];omega
  have hpEq:p=2*N:=by dsimp only [p];omega
  have hDpos:0<D:=by dsimp only [D];omega
  have hB':B.natDegree≤D:=by simpa [D,hGS] using hB
  rcases fiveToSix_zetaFirst_sparse_compensatedI4_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsource with
      ⟨i4,hi4⟩
  have hFce:Fce=(3/8:k)•C i4:=by
    dsimp only [Fce]
    linear_combination hi4
  rcases fiveToSix_zetaFirst_B3_compensatedI3_polynomial68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hsource with
      ⟨i3,hi3⟩
  have hRce:Rce=(3/4*gamma:k)•B^2+(9/8:k)•C i3:=by
    dsimp only [Rce,R]
    linear_combination hi3
  have hRceDeg:Rce.natDegree≤2*D:=by
    rw [hRce]
    compute_degree
    omega
  rcases had with ⟨j4,j3,hj4,hj3,hrow0,hrow1,hrow2,hpos,hiff⟩
  have hfull:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
        alpha gamma epsilon zeta eta A B c d e=0:=by
    exact hrow2
  have hfactor:=fiveToSix_zetaFirst_B3_equality_support_load_factor68
    (k:=k) gamma epsilon A B c d e
  change _ ∧ _ at hfactor
  have hdecomp:
      FiveToSixCuspZetaFirstB3EqualitySupportFullRowTwo68
          alpha gamma epsilon zeta eta A B c d e=
        (FiveToSixCuspZetaFirstB3EndpointRowTwoCore68 A B c d e-
          (9*gamma:k)•(A*derivative d)+
          (9/2*gamma:k)•(d*derivative A)+
          (9/4*epsilon:k)•(derivative A*B)-
          (9/2*epsilon:k)•(A*derivative B)+L)+W:=by
    dsimp only [W,L,
      FiveToSixCuspZetaFirstB3EqualitySupportNextRowTwoRemainder68]
    module
  have hrow:
      ((-(6:k)•(A*derivative Fce)+(3:k)•(derivative A*Fce)+
        (6:k)•derivative J)+L+W).coeff idx=0:=by
    have hc:=congrArg (fun Q:k[X]=>Q.coeff idx) hfull
    rw [hdecomp,hfactor.2] at hc
    simpa only [coeff_zero] using hc
  have hFconst:Fce=C (Fce.coeff 0):=by
    apply eq_C_of_natDegree_le_zero
    rw [hFce]
    compute_degree
  have hFder:derivative Fce=0:=by rw [hFconst,derivative_C]
  have hA'F:derivative A*Fce=Fce.coeff 0•derivative A:=by
    calc
      derivative A*Fce=derivative A*C (Fce.coeff 0):=by
        conv_lhs => rw [hFconst]
      _=Fce.coeff 0•derivative A:=by
        simp only [smul_eq_C_mul]
        ring
  rw [hFder,mul_zero,hA'F] at hrow
  simp only [coeff_add,coeff_smul,smul_eq_mul,coeff_derivative,
    zero_mul,coeff_zero] at hrow
  have hidxSucc:idx+1=p-1:=by dsimp only [idx];omega
  rw [hidxSucc] at hrow
  have hidxCast:((idx:k)+1)=((p-1:ℕ):k):=by exact_mod_cast hidxSucc
  rw [hidxCast] at hrow
  have hmain:(((p-1:ℕ):k))*
      ((3:k)*A.coeff (p-1)*Fce.coeff 0+
        (6:k)*J.coeff (p-1))+L.coeff idx+W.coeff idx=0:=by
    push_cast at hrow ⊢
    linear_combination hrow
  have hp1:0<p-1:=by omega
  have hpcast:(((p-1:ℕ):k))≠0:=by
    exact_mod_cast (show p-1≠0 by omega)
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68,
    D,p,idx,Fce,R,Rce,J,L,W]
  exact ⟨⟨hEq,hDT⟩,⟨i4,i3,hFce,hRce,hRceDeg⟩,hmain,hpcast⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_next68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroNext68

end Max11DegreeRoutes
