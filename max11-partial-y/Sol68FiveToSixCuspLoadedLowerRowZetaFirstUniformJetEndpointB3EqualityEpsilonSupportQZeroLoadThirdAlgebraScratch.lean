import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroJetThirdSourceScratch

/-! # Algebraic cancellation of the third `q=0` load

The four retained discriminant and compensated-`I4` jets annihilate the
complete third companion load.  The certificate is division-free after
multiplication by the nonzero cube of the leading `B` coefficient.
-/

noncomputable section

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixQZeroBBDJetZero68 (b0 d0:k):k := b0^2*d0

def FiveToSixQZeroBBDJetOne68 (b0 b1 d0 d1:k):k :=
  b0^2*d1+2*b0*b1*d0

def FiveToSixQZeroBBDJetTwo68 (b0 b1 b2 d0 d1 d2:k):k :=
  b0^2*d2+2*b0*b1*d1+(2*b0*b2+b1^2)*d0

def FiveToSixQZeroBBDJetThree68
    (b0 b1 b2 b3 d0 d1 d2 d3:k):k :=
  b0^2*d3+2*b0*b1*d2+(2*b0*b2+b1^2)*d1+
    (2*b0*b3+2*b1*b2)*d0

/-- The coefficient of `B^2*d'` three steps below its top. -/
def FiveToSixQZeroBBDerivativeJetThree68
    (P b0 b1 b2 b3 d0 d1 d2 d3:k):k :=
  (4/7*P-3)*b0^2*d3+2*(4/7*P-2)*b0*b1*d2+
    (4/7*P-1)*(2*b0*b2+b1^2)*d1+
    (4/7*P)*(2*b0*b3+2*b1*b2)*d0

def FiveToSixQZeroBBDerivativeJetTwo68
    (P b0 b1 b2 d0 d1 d2:k):k :=
  (4/7*P-2)*b0^2*d2+2*(4/7*P-1)*b0*b1*d1+
    (4/7*P)*(2*b0*b2+b1^2)*d0

def FiveToSixQZeroBBDerivativeJetOne68
    (P b0 b1 d0 d1:k):k :=
  (4/7*P-1)*b0^2*d1+2*(4/7*P)*b0*b1*d0

def FiveToSixQZeroBBDerivativeJetZero68 (P b0 d0:k):k :=
  (4/7*P)*b0^2*d0

/-- The order-three coefficient of `B*c*e'`. -/
def FiveToSixQZeroBCEDerivativeJetThree68
    (P b0 b1 b2 b3 c0 c1 c2 c3 e0 e1 e2 e3:k):k :=
  (15/14*P)*(b0*c3+b1*c2+b2*c1+b3*c0)*e0+
    (15/14*P-1)*(b0*c2+b1*c1+b2*c0)*e1+
    (15/14*P-2)*(b0*c1+b1*c0)*e2+
    (15/14*P-3)*b0*c0*e3

/-- The order-three coefficient of `c*c'*d`, symmetrized using
`2*c*c'=(c^2)'`. -/
def FiveToSixQZeroCCDerivativeDJetThree68
    (P c0 c1 c2 c3 d0 d1 d2 d3:k):k :=
  (1/2:k)*((10/7*P-3)*(2*c0*c3+2*c1*c2)*d0+
    (10/7*P-2)*(2*c0*c2+c1^2)*d1+
    (10/7*P-1)*(2*c0*c1)*d2+
    (10/7*P)*c0^2*d3)

/-- Normalized order-three row-zero load, with all degree weights written in
terms of the top `A` degree `P`. -/
def FiveToSixQZeroRowZeroLoadJetThree68
    (P a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      d0 d1 d2 d3 e0 e1 e2 e3:k):k :=
  (1/2:k)*a0*((P-3)*
      FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3+
    FiveToSixQZeroBBDerivativeJetThree68 P b0 b1 b2 b3 d0 d1 d2 d3)+
  (1/2:k)*a1*((P-2)*
      FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2+
    FiveToSixQZeroBBDerivativeJetTwo68 P b0 b1 b2 d0 d1 d2)+
  (1/2:k)*a2*((P-1)*
      FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1+
    FiveToSixQZeroBBDerivativeJetOne68 P b0 b1 d0 d1)+
  (1/2:k)*a3*(P*FiveToSixQZeroBBDJetZero68 b0 d0+
    FiveToSixQZeroBBDerivativeJetZero68 P b0 d0)-
  3*FiveToSixQZeroBCEDerivativeJetThree68 P
    b0 b1 b2 b3 c0 c1 c2 c3 e0 e1 e2 e3+
  3*FiveToSixQZeroCCDerivativeDJetThree68 P
    c0 c1 c2 c3 d0 d1 d2 d3

/-- Exact polynomial certificate for the third load.  This is the order-three
analogue of `fiveToSix_..._second_load_algebra68`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_third_load_algebra68
    (P a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
      d0 d1 d2 d3 e0 e1 e2 e3:k)
    (hb0:b0≠0)
    (hD0:a0*b0^2+3*c0^2=0)
    (hD1:a1*b0^2+2*a0*b0*b1+6*c0*c1=0)
    (hD2:a2*b0^2+2*a1*b0*b1+a0*(2*b0*b2+b1^2)+
      3*(2*c0*c2+c1^2)=0)
    (hD3:a3*b0^2+2*a2*b0*b1+
      a1*(2*b0*b2+b1^2)+a0*(2*b0*b3+2*b1*b2)+
      6*(c0*c3+c1*c2)=0)
    (hI40:b0*e0+c0*d0=0)
    (hI41:b1*e0+b0*e1+c1*d0+c0*d1=0)
    (hI42:b2*e0+b1*e1+b0*e2+c2*d0+c1*d1+c0*d2=0)
    (hI43:b3*e0+b2*e1+b1*e2+b0*e3+
      c3*d0+c2*d1+c1*d2+c0*d3=0):
    6*(P-3)^2*(P-2)*(P-1)*a3*b0^2*d0+
      6*(P-3)*(P-2)*(P-1)*
        FiveToSixQZeroRowZeroLoadJetThree68 P
          a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
          d0 d1 d2 d3 e0 e1 e2 e3+
      P*(P-2)*(P-1)*a0*(6*(P-3)*
        FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3)+
      (P-3)*(P-1)^2*a1*(6*(P-2)*
        FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2)+
      (P-3)*(P-2)^2*a2*(6*(P-1)*
        FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1)=0:=by
  have hmul:b0^3*(
      6*(P-3)^2*(P-2)*(P-1)*a3*b0^2*d0+
        6*(P-3)*(P-2)*(P-1)*
          FiveToSixQZeroRowZeroLoadJetThree68 P
            a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3
            d0 d1 d2 d3 e0 e1 e2 e3+
        P*(P-2)*(P-1)*a0*(6*(P-3)*
          FiveToSixQZeroBBDJetThree68 b0 b1 b2 b3 d0 d1 d2 d3)+
        (P-3)*(P-1)^2*a1*(6*(P-2)*
          FiveToSixQZeroBBDJetTwo68 b0 b1 b2 d0 d1 d2)+
        (P-3)*(P-2)^2*a2*(6*(P-1)*
          FiveToSixQZeroBBDJetOne68 b0 b1 d0 d1))=0:=by
    dsimp only [FiveToSixQZeroRowZeroLoadJetThree68,
      FiveToSixQZeroBBDJetZero68,FiveToSixQZeroBBDJetOne68,
      FiveToSixQZeroBBDJetTwo68,FiveToSixQZeroBBDJetThree68,
      FiveToSixQZeroBBDerivativeJetZero68,
      FiveToSixQZeroBBDerivativeJetOne68,
      FiveToSixQZeroBBDerivativeJetTwo68,
      FiveToSixQZeroBBDerivativeJetThree68,
      FiveToSixQZeroBCEDerivativeJetThree68,
      FiveToSixQZeroCCDerivativeDJetThree68]
    linear_combination
      (3/7:k)*b0^3*d0*(P-3)*(P-2)*(P-1)*(25*P-42)*hD3+
      (3/7:k)*b0^2*(P-3)*(P-2)*(P-1)*
        ((25*P-42)*b0*d1+14*b1*d0)*hD2+
      (3/7:k)*b0*(P-3)*(P-2)*(P-1)*
        ((25*P-42)*b0^2*d2+14*b0*b1*d1+
          28*b0*b2*d0-14*b1^2*d0)*hD1+
      (3/7:k)*(P-3)*(P-2)*(P-1)*
        ((25*P-42)*b0^3*d3+14*b0^2*b1*d2+
          28*b0^2*b2*d1+42*b0^2*b3*d0-
          14*b0*b1^2*d1-42*b0*b1*b2*d0+14*b1^3*d0)*hD0-
      (27/7:k)*b0^3*c0*(P-3)*(P-2)*(P-1)*(5*P-14)*hI43-
      (9/7:k)*b0^2*(P-3)*(P-2)*(P-1)*
        ((15*P-28)*b0*c1+14*b1*c0)*hI42-
      (9/7:k)*b0*(P-3)*(P-2)*(P-1)*
        ((15*P-14)*b0^2*c2+14*b0*b1*c1+
          28*b0*b2*c0-14*b1^2*c0)*hI41-
      (9/7:k)*(P-3)*(P-2)*(P-1)*
        (15*P*b0^3*c3+14*b0^2*b1*c2+
          28*b0^2*b2*c1+42*b0^2*b3*c0-
          14*b0*b1^2*c1-42*b0*b1*b2*c0+14*b1^3*c0)*hI40
  have hb03:b0^3≠0:=pow_ne_zero 3 hb0
  exact (mul_eq_zero.mp hmul).resolve_left hb03

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_third_load_algebra68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroLoadThirdAlgebra68

end Max11DegreeRoutes
