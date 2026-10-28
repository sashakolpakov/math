import OAI.Geometry.Nikodym.Abstract.EndpointLength

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

/-- An increasing differentiable reparametrization of an inverse chart
segment retains its actual ambient Riemannian length. -/
theorem pathELength_inverse_segment_reparam {a b : E} {s : ℝ → ℝ} {T : ℝ}
    (hseg : segment ℝ a b ⊆ C.manifoldChart.target) (hT : 0 ≤ T)
    (hmono : MonotoneOn s (Icc 0 T))
    (hdiff : DifferentiableOn ℝ s (Icc 0 T))
    (hs0 : s 0 = 0) (hsT : s T = 1) :
    pathELength 𝓘(ℝ,E) (C.manifoldChart.symm ∘ (AffineMap.lineMap a b ∘ s)) 0 T =
      ENNReal.ofReal (beltramiSegmentLength κ a b) := by
  have hd : MDifferentiableOn 𝓘(ℝ) 𝓘(ℝ,E)
      (C.manifoldChart.symm ∘ AffineMap.lineMap a b) (Icc (s 0) (s T)) := by
    rw [hs0,hsT]
    intro t ht
    have hy := hseg (lineMap_mem_segment ℝ a b ht)
    have hi := ((C.manifoldChart_inverse_smooth _ hy).contMDiffAt
      (C.manifoldChart.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
    exact (hi.comp t AffineMap.hasDerivAt_lineMap.differentiableAt.mdifferentiableAt).mdifferentiableWithinAt
  have he := pathELength_comp_of_monotoneOn (I:=𝓘(ℝ,E)) hT hmono hdiff hd
  rw [hs0,hsT] at he
  exact he.trans (C.pathELength_inverse_segment hseg)

end OAI.Geometry.Nikodym.LocalBeltramiChart
