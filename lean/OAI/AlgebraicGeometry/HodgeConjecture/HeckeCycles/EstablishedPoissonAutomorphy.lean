import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Established Poisson Automorphy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedPoissonAutomorphy.CM

/-! Discharge the complete PoissonAutomorphy prerequisite by its genuine proof. The
statement-type audit is checked in a separate module because the proof
and the committed statement use the same declaration name. -/

universe u v w t

theorem full_input : PoissonAutomorphy.CM.PoissonAutomorphyInput :=
  RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.poisson_summation_and_rational_theta_automorphy

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedPoissonAutomorphy.CM
