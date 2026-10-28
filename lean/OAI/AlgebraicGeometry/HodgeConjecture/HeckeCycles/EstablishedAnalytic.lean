import OAI.RepresentationTheory.Theta.CompletionAnalysis
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CotangentBundleTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Transport

/-! # Established Analytic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAnalytic.CM

/-! Prove the complete determinant/cotangent and completed-theta inputs
in the original HeckeCycles consumer interfaces. The established transports retain
every operation, hypothesis, and conclusion, including the uncompleted
Poisson antecedent of CompletedTheta. No conclusion is supplied as a new input. -/

universe u v

theorem determinant_cotangent_supplier :
    RepresentationTheory.Theta.Adelic.Prerequisites.CotangentBundleInput :=
  Geometry.ComplexBall.CotangentBundle.determinant_and_cotangent_identities

theorem determinant_cotangent :
    ∀ (B : Type u) (A : Type v) [CommSemiring B] [CommGroup A],
      @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _ :=
  CotangentBundleTransport.CM.full_input_iff.mp determinant_cotangent_supplier

theorem completed_theta_supplier :
    RepresentationTheory.Theta.Adelic.Prerequisites.ThetaInput :=
  RepresentationTheory.Theta.CompletionAnalysis.completed_theta_tensor_transformation

theorem completed_theta :
    ∀ (I : Type u) [Fintype I] [DecidableEq I],
      @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _ :=
  Theta.Transport.CM.full_input_iff.mp completed_theta_supplier

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAnalytic.CM
