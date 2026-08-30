import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI3NextScratch

/-! # Exact first-jet rank on the `q=0` wall

The compensated-I3 tangent is dependent on the cusp and compensated-I4
tangents.  Modulo those two tangent rows, the explicit source companion
collapses to a single entry, proportional to `Fce_0 * A_(p-1)`.  Thus the
first-jet system has rank three when `Fce_0` is nonzero and rank two when it
vanishes; in either case it remains positive-dimensional.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetRank68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The compensated-I3 tangent is forced by the cusp and compensated-I4
tangents together with their top equations. -/
theorem fiveToSix_qZero_I3_tangent_dependency_algebra68
    (a b c d e a1 b1 c1 d1 e1:k)
    (hb:b≠0)
    (hcusp:a*b^2+3*c^2=0)
    (hi4:b*e+c*d=0)
    (hdisc:a1*b^2+2*a*b*b1+6*c*c1=0)
    (hi4next:b1*e+b*e1+c1*d+c*d1=0):
    a1*b*d+a*b1*d+a*b*d1-3*(c1*e+c*e1)=0:=by
  have hi3top:a*b*d-3*c*e=0:=by
    apply (mul_left_cancel₀ hb)
    linear_combination d*hcusp-3*c*hi4
  apply (mul_left_cancel₀ hb)
  linear_combination d*hdisc-3*c*hi4next-b1*hi3top-
    3*c1*hi4+d1*hcusp

/-- Pure algebraic row reduction of the complete first-jet companion. -/
theorem fiveToSix_qZero_firstJet_companion_collapse_algebra68
    (P D C V E a b c d e a1 b1 c1 d1 e1 f:k)
    (hb:b≠0)
    (hdeg:P+D+V-C-E=0)
    (hcusp:a*b^2+3*c^2=0)
    (hi4:b*e+c*d=0)
    (hdisc:a1*b^2+2*a*b*b1+6*c*c1=0)
    (hi4next:b1*e+b*e1+c1*d+c*d1=0)
    (hcomp:
      a1*(3*(2*P-1)*a*f+2*(P-1)*b^2*d)+
      2*((V+D)*a1*b^2*d+
        (2*(V+D)-1)*a*b*b1*d+
        (V+D-1)*a*b^2*d1-
        3*(E*b1*c*e+E*b*c1*e+(E-1)*b*c*e1)+
        3*((2*C-1)*c*c1*d+C*c^2*d1))+
      2*P*a*(b^2*d1+2*b*b1*d)=0):
    3*(2*P-1)*a*f*a1=0:=by
  have hi3top:a*b*d-3*c*e=0:=by
    apply (mul_left_cancel₀ hb)
    linear_combination d*hcusp-3*c*hi4
  linear_combination
    hcomp-
    2*(P+D+V-1)*d*hdisc+
    6*(E-1)*c*hi4next-
    2*b1*hi3top+
    6*E*c1*hi4-
    2*(P+D+V-1)*d1*hcusp+
    (12*c*d*c1+6*c^2*d1)*hdeg

/-- The nonzero `3 x 3` minor, on columns `(A_(p-1), B_(D-1),
e_(E-1))`, after exact row reduction. -/
theorem fiveToSix_qZero_firstJet_reduced_minor68
    (P a b f:k):
    b^2*((0:k)*0-b*0)-2*a*b*(0*0-b*(3*(2*P-1)*a*f))=
      6*(2*P-1)*a^2*b^2*f:=by
  ring

/-- Source-backed rank reduction: the only first-jet information in the
companion beyond the cusp and compensated-I4 tangents is
`Fce_0 * A_(p-1)=0`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_jet_rank68
    (alpha gamma epsilon zeta eta terminal:k)
    (A B c d e:k[X]) (N G S:ℕ)
    (hs:FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq:9*N-7*S=0):
    let p:=2*N
    let D:=3*N-2*S
    let Cc:=4*N-2*S
    let V:=5*N-3*S
    let E:=6*N-3*S
    let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
      (3/4*epsilon:k)•B
    Fce.coeff 0*A.coeff (p-1)=0:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
  let Fce:=((B*e+c*d)-(1/9:k)•B^3)+(3/2*gamma:k)•d+
    (3/4*epsilon:k)•B
  change Fce.coeff 0*A.coeff (p-1)=0
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
  have ha0:A.coeff p≠0:=by simpa [p] using hatop
  have hb0:B.coeff D≠0:=by simpa [D,hGS] using hBtop
  have hcuspEq':A.coeff p*B.coeff D^2+3*c.coeff Cc^2=0:=by
    simpa [p,D,Cc,hGS] using hcuspEq
  have htop:=fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at htop
  have hi4:B.coeff D*e.coeff E+c.coeff Cc*d.coeff V=0:=htop.1
  have hdisc:=fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hdisc
  have hi4next:=fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hi4next
  have hjet:=fiveToSix_zetaFirst_B3_equality_support_qZero_jet_reduction68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroRowZeroJet68]
    at hjet
  have hp:0<p:=by dsimp only [p];omega
  have hD:0<D:=by dsimp only [D];omega
  have hC:0<Cc:=by dsimp only [Cc];omega
  have hV:0<V:=by dsimp only [V];omega
  have hE:0<E:=by dsimp only [E];omega
  have hp1:(((p-1:ℕ):k))=(p:k)-1:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have h2p1:(((2*p-1:ℕ):k))=2*(p:k)-1:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hVD1:(((V+D-1:ℕ):k))=(V:k)+(D:k)-1:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have h2VD1:(((2*(V+D)-1:ℕ):k))=2*((V:k)+(D:k))-1:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hE1:(((E-1:ℕ):k))=(E:k)-1:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have h2C1:(((2*Cc-1:ℕ):k))=2*(Cc:k)-1:=by
    rw [Nat.cast_sub (by omega)];norm_num
  have hp1N:(((2*N-1:ℕ):k))=(p:k)-1:=by simpa [p] using hp1
  have h2p1N:(((2*(2*N)-1:ℕ):k))=2*(p:k)-1:=by
    simpa [p] using h2p1
  rw [hp1N,h2p1N] at hjet
  have hdegNat:p+D+V=Cc+E:=by dsimp only [p,D,Cc,V,E];omega
  have hdegCast:(p:k)+(D:k)+(V:k)=(Cc:k)+(E:k):=by
    exact_mod_cast hdegNat
  have hdeg:((p:k)+(D:k)+(V:k)-(Cc:k)-(E:k))=0:=by
    linear_combination hdegCast
  have hcollapse:=fiveToSix_qZero_firstJet_companion_collapse_algebra68
    (P:=(p:k)) (D:=(D:k)) (C:=(Cc:k)) (V:=(V:k)) (E:=(E:k))
    (a:=A.coeff p) (b:=B.coeff D) (c:=c.coeff Cc)
    (d:=d.coeff V) (e:=e.coeff E)
    (a1:=A.coeff (p-1)) (b1:=B.coeff (D-1))
    (c1:=c.coeff (Cc-1)) (d1:=d.coeff (V-1))
    (e1:=e.coeff (E-1)) (f:=Fce.coeff 0)
    hb0 hdeg hcuspEq' hi4 hdisc hi4next (by
      convert hjet using 1 <;> ring)
  have hfactor:(3:k)*(2*(p:k)-1)*A.coeff p≠0:=by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) ha0
    have hnat:2*p-1≠0:=by omega
    have hcast:(((2*p-1:ℕ):k))≠0:=Nat.cast_ne_zero.mpr hnat
    rwa [h2p1] at hcast
  apply (mul_left_cancel₀ hfactor)
  linear_combination hcollapse

#print axioms fiveToSix_qZero_I3_tangent_dependency_algebra68
#print axioms fiveToSix_qZero_firstJet_companion_collapse_algebra68
#print axioms fiveToSix_qZero_firstJet_reduced_minor68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_jet_rank68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetRank68

end Max11DegreeRoutes
