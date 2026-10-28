import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DefinitionsIntegral
import OAI.RepresentationTheory.Theta.Geometric.Torus.Data

/-! # Projective Period Data -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProjectivePeriodData.Geometric

noncomputable section

/-! The checked ThetaConstruction quotient as generic projective period data. -/

def projectivePeriodData {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g}
    (T : DefinitionsIntegral.MarkedPolarizedTorus g E) :
    RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData := by
  letI : DiscreteTopology T.lattice := T.discrete
  letI : CompactSpace (DefinitionsIntegral.Tangent g ⧸ T.lattice) := T.compact
  exact RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.ofCompactProjectiveTorus
    (DefinitionsIntegral.Tangent g) T.lattice T.projective

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProjectivePeriodData.Geometric
