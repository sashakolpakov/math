import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.InverseEquation

/-! # Graph Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.GraphPullback.BundleCycles

noncomputable section

/-! The constructed Chow pullback satisfies the complete geometric graph
equation in every dimension grade for every morphism of presentations. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphChowPullback_graphEquation (a : Chow.BundleCycles.ChowQ Y p) (d : ℕ) :
    GraphNormal.ChowFamily.BundleCycles.graphNormalChowFamily f p d (Graph.ChowPullback.BundleCycles.graphChowPullback f p a) =
      Global.ChowSpecialization.BundleCycles.globalChowSpecialization (Graph.OpenAmbient.BundleCycles.graph f).ker (Graph.Chow.BundleCycles.graphAmbientStructureMap f) d (Graph.ProjectionChowFamily.BundleCycles.graphProjectionChowFamily f p d a) := by
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective Y p a
  rw [Graph.ChowPullback.BundleCycles.graphChowPullback_cycle, Graph.ProjectionChowFamily.BundleCycles.graphProjectionChowFamily_cycle, Global.ChowPointSpecialization.BundleCycles.globalChowSpecialization_pointClass]
  exact GraphNormal.InverseEquation.BundleCycles.graphNormalInverseChow_equation_of_codimension f p _
    (Graph.SpecializationCycleCodimension.BundleCycles.graphProjectionSpecialization_cycle_codimension f p z) d

theorem graphChowPullback_isGeometric : MapCharacterization.BundleCycles.IsGeometricGraphPullback f p (Graph.ChowPullback.BundleCycles.graphChowPullback f p) :=
  ⟨Graph.ProjectionChowFamily.BundleCycles.graphProjectionChowFamily f p, GraphNormal.ChowFamily.BundleCycles.graphNormalChowFamily f p,
    Graph.ProjectionChowFamily.BundleCycles.graphProjectionChowFamily_isGeometric f p, GraphNormal.ChowFamily.BundleCycles.graphNormalChowFamily_isGeometric f p,
    GraphNormal.ChowFamily.BundleCycles.graphNormalChowFamily_joint_injective f p, graphChowPullback_graphEquation f p⟩

theorem geometricGraphPullback_exists_unique :
    ∃! pull : Chow.BundleCycles.ChowQ Y p ⟶ Chow.BundleCycles.ChowQ X p, MapCharacterization.BundleCycles.IsGeometricGraphPullback f p pull :=
  ⟨Graph.ChowPullback.BundleCycles.graphChowPullback f p, graphChowPullback_isGeometric f p, fun _ h =>
    MapCharacterization.BundleCycles.isGeometricGraphPullback_unique f p _ _ h (graphChowPullback_isGeometric f p)⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.GraphPullback.BundleCycles
