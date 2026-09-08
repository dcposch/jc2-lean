import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroI3NextTwoScratch

/-! # Exact second-jet incidence rank on `q=0`

The second compensated-I3 row is an exact convolutional consequence of the
discriminant and compensated-I4 rows through orders zero, one, and two.  The
two independent rows solve uniquely for `A_(p-2)` and `e_(E-2)`, leaving
`B_(D-2), c_(C-2), d_(V-2)` as three residual second-jet directions until a
new source companion is extracted.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetTwoRank68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact order-two form of the identity
`B*(A*B*d-3*c*e)=d*(A*B^2+3*c^2)-3*c*(B*e+c*d)`. -/
theorem fiveToSix_qZero_I3_secondJet_dependency_algebra68
    (a b c d e a1 b1 c1 d1 e1 a2 b2 c2 d2 e2:k)
    (hb:b≠0)
    (hcusp:a*b^2+3*c^2=0)
    (hi4:b*e+c*d=0)
    (hdisc1:a1*b^2+2*a*b*b1+6*c*c1=0)
    (hi41:b1*e+b*e1+c1*d+c*d1=0)
    (hdisc2:a2*b^2+2*a1*b*b1+
      a*(2*b*b2+b1^2)+3*(2*c*c2+c1^2)=0)
    (hi42:b2*e+b1*e1+b*e2+c2*d+c1*d1+c*d2=0):
    a2*b*d+a1*b1*d+a*b2*d+a1*b*d1+a*b1*d1+a*b*d2-
      3*(c2*e+c1*e1+c*e2)=0:=by
  have hi3top:a*b*d-3*c*e=0:=by
    apply (mul_left_cancel₀ hb)
    linear_combination d*hcusp-3*c*hi4
  have hi31:a1*b*d+a*b1*d+a*b*d1-3*(c1*e+c*e1)=0:=
    fiveToSix_qZero_I3_tangent_dependency_algebra68
      a b c d e a1 b1 c1 d1 e1 hb hcusp hi4 hdisc1 hi41
  apply (mul_left_cancel₀ hb)
  linear_combination d*hdisc2+d1*hdisc1+d2*hcusp-
    3*c*hi42-3*c1*hi41-3*c2*hi4-b1*hi31-b2*hi3top

/-- The independent second-jet minor on columns `(a2,e2)` is `b^3`. -/
theorem fiveToSix_qZero_secondJet_minor_ne_zero68 (b:k) (hb:b≠0):
    b^2*b≠0:=mul_ne_zero (pow_ne_zero 2 hb) hb

/-- Exact solution of the two independent second-jet incidence rows.  The
three entries `b2,c2,d2` remain free parameters at this stage. -/
theorem fiveToSix_qZero_secondJet_solved_algebra68
    (a b c d e a1 b1 c1 d1 e1 a2 b2 c2 d2 e2:k)
    (hb:b≠0)
    (hdisc2:a2*b^2+2*a1*b*b1+
      a*(2*b*b2+b1^2)+3*(2*c*c2+c1^2)=0)
    (hi42:b2*e+b1*e1+b*e2+c2*d+c1*d1+c*d2=0):
    a2=-(2*a1*b*b1+a*(2*b*b2+b1^2)+3*(2*c*c2+c1^2))/b^2 ∧
    e2=-(b2*e+b1*e1+c2*d+c1*d1+c*d2)/b:=by
  constructor
  · apply (eq_div_iff (pow_ne_zero 2 hb)).2
    linear_combination hdisc2
  · apply (eq_div_iff hb).2
    linear_combination hi42

/-- Source-backed solved second-jet packet, exhibiting exactly three residual
new-variable directions before any additional companion equation. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_secondJet_rank68
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
    A.coeff (p-2)=
      -((2:k)*A.coeff (p-1)*B.coeff D*B.coeff (D-1)+
        A.coeff p*((2:k)*B.coeff D*B.coeff (D-2)+B.coeff (D-1)^2)+
        (3:k)*((2:k)*c.coeff Cc*c.coeff (Cc-2)+c.coeff (Cc-1)^2))/
          B.coeff D^2 ∧
    e.coeff (E-2)=
      -(B.coeff (D-2)*e.coeff E+B.coeff (D-1)*e.coeff (E-1)+
        c.coeff (Cc-2)*d.coeff V+c.coeff (Cc-1)*d.coeff (V-1)+
        c.coeff Cc*d.coeff (V-2))/B.coeff D:=by
  let p:=2*N
  let D:=3*N-2*S
  let Cc:=4*N-2*S
  let V:=5*N-3*S
  let E:=6*N-3*S
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
  have hdisc2:=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hdisc2
  have hi42:=fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hi42
  exact fiveToSix_qZero_secondJet_solved_algebra68
    (A.coeff p) (B.coeff D) (c.coeff Cc) (d.coeff V) (e.coeff E)
    (A.coeff (p-1)) (B.coeff (D-1)) (c.coeff (Cc-1))
    (d.coeff (V-1)) (e.coeff (E-1))
    (A.coeff (p-2)) (B.coeff (D-2)) (c.coeff (Cc-2))
    (d.coeff (V-2)) (e.coeff (E-2)) hb0 hdisc2 (by
      linear_combination hi42)

#print axioms fiveToSix_qZero_I3_secondJet_dependency_algebra68
#print axioms fiveToSix_qZero_secondJet_minor_ne_zero68
#print axioms fiveToSix_qZero_secondJet_solved_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_secondJet_rank68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetTwoRank68

end Max11DegreeRoutes
