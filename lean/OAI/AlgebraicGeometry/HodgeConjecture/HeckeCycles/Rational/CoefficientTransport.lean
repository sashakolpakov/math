import OAI.RepresentationTheory.Theta.Geometric.Period.Ne

/-! # Coefficient Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.CoefficientTransport.CM

noncomputable section

/-! Equality of the Hermitian coefficient transports the actual rational
unitary group while preserving its matrices and entire ball action. -/

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
  (b c : E) (h : b = c)

def equivalence : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b ≃* Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU c := by
  subst c
  exact MulEquiv.refl _

theorem matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) : (equivalence b c h g).val = g.val := by
  subst c
  rfl

theorem period (μ : E →+* ℂ) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm b μ g =
      RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm c μ (equivalence b c h g) := by
  subst c
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.CoefficientTransport.CM
