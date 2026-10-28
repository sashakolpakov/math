import OAI.Geometry.Nikodym.Sectional.Definition
import OAI.Geometry.Nikodym.SpaceFormChart

noncomputable section
namespace OAI.Geometry.Nikodym

/-- The genuine local space-form chart follows from the scalar sectional
curvature condition, not an assumed tensor formula or model chart. -/
theorem SmoothCoordinateMetric.nonempty_localBeltramiChart_of_sectional {n : ℕ}
    (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))) {κ : ℝ}
    (hκ : g.HasConstantSectionalCurvature κ) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ g.domain) : Nonempty (LocalBeltramiChart g κ x₀) :=
  g.nonempty_localBeltramiChart (OAI.Geometry.Nikodym.SmoothCoordinateMetric.HasConstantSectionalCurvature.tensor_identity g hκ) hx₀

end OAI.Geometry.Nikodym
