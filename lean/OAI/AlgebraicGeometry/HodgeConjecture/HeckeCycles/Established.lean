import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.Theta
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Action
import OAI.RepresentationTheory.Theta.Geometric.Theorem

/-! # Established -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Established.CM.Hecke

noncomputable section

/-! The full constructed Hecke and theta covariance theorems supply the
complete original HeckeCycles consumer propositions. No conclusion is projected
away and no compatibility premise is added. -/

theorem spherical_hecke : TateComparison.CM.TateComparisonInput :=
  AbelianScheme.TateComparison.Action.spherical_hecke_algebra_action_constructed

theorem theta_covariance : Geometric.Theta.CM.GeometricThetaInput :=
  RepresentationTheory.Theta.Geometric.Theorem.active_hecke_action_and_finite_weil_covariance_constructed

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Established.CM.Hecke
