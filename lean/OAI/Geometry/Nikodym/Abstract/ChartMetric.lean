import OAI.Geometry.Nikodym.Abstract.Chart

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology ContDiff Bundle RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace LocalBeltramiChart

omit [FiniteDimensional ℝ E] in
theorem inverse_metric {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
    (C : LocalBeltramiChart g κ x₀) {y : E} (hy : y ∈ C.chart.target) (u v : E) :
    g.inner (C.chart.symm y)
      (fderiv ℝ (C.chart.symm : E → E) y u)
      (fderiv ℝ (C.chart.symm : E → E) y v) = beltramiMetric κ y u v := by
  have hx := C.chart.map_target hy
  have hf := ((C.smooth _ hx).contDiffAt (C.chart.open_source.mem_nhds hx)).differentiableAt
    (by simp)
  have hi := ((C.inverse_smooth _ hy).contDiffAt (C.chart.open_target.mem_nhds hy)).differentiableAt
    (by simp)
  have he : (C.chart : E → E) ∘ C.chart.symm =ᶠ[𝓝 y] id := by
    filter_upwards [C.chart.open_target.mem_nhds hy] with z hz
    exact C.chart.right_inv hz
  have hd := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp y hf hi,fderiv_id] at hd
  have hu : fderiv ℝ (C.chart : E → E) (C.chart.symm y)
      (fderiv ℝ (C.chart.symm : E → E) y u) = u :=
    congrArg (fun L : E →L[ℝ] E => L u) hd
  have hv : fderiv ℝ (C.chart : E → E) (C.chart.symm y)
      (fderiv ℝ (C.chart.symm : E → E) y v) = v :=
    congrArg (fun L : E →L[ℝ] E => L v) hd
  rw [C.metric _ hx,C.chart.right_inv hy,hu,hv]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

/-- Exact metric pullback for the actual manifold Beltrami chart. -/
theorem manifoldChart_inverse_metric {y : E} (hy : y ∈ C.manifoldChart.target) (u v : E) :
    ⟪mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.manifoldChart.symm y u,
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.manifoldChart.symm y v⟫ = beltramiMetric κ y u v := by
  have hyC : y ∈ C.chart.target := C.manifoldChart_target ▸ hy
  have hx : C.chart.symm y ∈ (extChartAt 𝓘(ℝ,E) p).target :=
    C.source_domain (C.chart.map_target hyC)
  have hi := ((C.inverse_smooth y hyC).contDiffAt
    (C.chart.open_target.mem_nhds hyC)).contMDiffAt.mdifferentiableAt (by simp)
  have ha := ((contMDiffOn_extChartAt_symm (I:=𝓘(ℝ,E)) (n:=∞) p _ hx).contMDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hx)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp y ha hi
  change ⟪mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
      ((extChartAt 𝓘(ℝ,E) p).symm ∘ C.chart.symm) y u,
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E)
      ((extChartAt 𝓘(ℝ,E) p).symm ∘ C.chart.symm) y v⟫ = _
  rw [hd]
  change ⟪mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm (C.chart.symm y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.chart.symm y u),
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) p).symm (C.chart.symm y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) C.chart.symm y v)⟫ = _
  have hmetric := C.inverse_metric hyC u v
  rw [abstractChartMetric_inner] at hmetric
  simpa only [mfderiv_eq_fderiv] using! hmetric

end LocalBeltramiChart
end OAI.Geometry.Nikodym
