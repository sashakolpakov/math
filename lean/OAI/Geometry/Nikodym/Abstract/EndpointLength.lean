import OAI.Geometry.Nikodym.Abstract.Length
import OAI.Geometry.Nikodym.EndpointLength
import Mathlib.Analysis.Calculus.Deriv.AffineMap

noncomputable section
open Set Bundle Manifold
open scoped Topology ContDiff Bundle ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

/-- A chart segment's endpoint length is exactly the actual Riemannian
length of its inverse image in the original manifold. -/
theorem pathELength_inverse_segment {a b : E}
    (hseg : segment ℝ a b ⊆ C.manifoldChart.target) :
    pathELength 𝓘(ℝ,E) (C.manifoldChart.symm ∘ AffineMap.lineMap a b) 0 1 =
      ENNReal.ofReal (beltramiSegmentLength κ a b) := by
  have hi : MapsTo (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) C.manifoldChart.target := by
    intro t ht
    exact hseg (by
      rw [segment_eq_image']
      refine ⟨t,ht,?_⟩
      simp only [AffineMap.lineMap_apply_module]
      module)
  rw [C.pathELength_manifoldChart_inverse
    (fun t _ => (AffineMap.hasDerivAt_lineMap : HasDerivAt
      (AffineMap.lineMap a b : ℝ → E) (b-a) t)) hi]
  apply beltramiPathLength_segment_eq
  intro t ht
  have hy : AffineMap.lineMap a b t ∈ C.chart.target := C.manifoldChart_target ▸ hi ht
  have hp := C.positive _ (C.chart.map_target hy)
  rw [C.chart.right_inv hy] at hp
  exact hp.ne'

end OAI.Geometry.Nikodym.LocalBeltramiChart
