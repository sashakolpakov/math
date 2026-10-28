import OAI.Geometry.Nikodym.Abstract.Chart
import OAI.Geometry.Nikodym.Sectional.Chart

noncomputable section
open Set Bundle Manifold
open scoped Topology ContDiff Bundle

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

/-- Constant sectional curvature expressed by the Levi-Civita curvature
of the actual pulled-back Riemannian metric in each ordinary atlas chart.
The scalar condition is imposed only on nondegenerate planes. -/
def AtlasConstantSectionalCurvature (κ : ℝ) : Prop :=
  ∀ p : M, (abstractChartMetric (E:=E) p).HasConstantSectionalCurvature κ

theorem nonempty_manifold_localBeltramiChart {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n)) (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
    (p : M) {κ : ℝ}
    (hκ : (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).HasConstantSectionalCurvature κ) :
    Nonempty (LocalBeltramiChart (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p) κ
      (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p p)) :=
  (abstractChartMetric p).nonempty_localBeltramiChart_of_sectional hκ
    (abstractChartMetric_base_mem p)

end OAI.Geometry.Nikodym
