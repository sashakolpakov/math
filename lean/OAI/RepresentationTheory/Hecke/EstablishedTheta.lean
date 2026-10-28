import OAI.RepresentationTheory.Hecke.SphericalAction
import OAI.RepresentationTheory.Theta.Geometric.Theorem
import OAI.RepresentationTheory.Hecke.RadialDilation.AnalyticDilation
import OAI.RepresentationTheory.Weil.Local.Formulas
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Established Theta -/

namespace OAI.RepresentationTheory.Hecke.EstablishedTheta.CentralConstraintIntrinsic

/-! Complete prerequisite propositions, discharged by the constructed
theorems rather than by selected consequences or placeholder statements. -/

theorem proved_theta_covariance_input : SphericalAction.GeometricThetaInput :=
  Theta.Geometric.Theorem.active_hecke_action_and_finite_weil_covariance_constructed

theorem proved_dilation_input : SphericalAction.RadialDilationInput :=
  RadialDilation.AnalyticDilation.Analytic.algebraic_dilation_relation

theorem proved_local_weil_input : RadialDilation.Prerequisites.Core.LocalWeil.Proposition :=
  Weil.Local.Formulas.schrodinger_generator_formulas

theorem proved_poisson_input : RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition := by
  intro ι _ _ MpR MpF MpA _ _ _ D γ
  exact Theta.PoissonAutomorphyGaussianParabolic.poisson_summation_and_rational_theta_automorphy D γ

end OAI.RepresentationTheory.Hecke.EstablishedTheta.CentralConstraintIntrinsic
