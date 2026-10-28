import OAI.Geometry.Nikodym.Abstract.Metric
import OAI.Geometry.Nikodym.SpaceFormChart

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology ContDiff Bundle RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

theorem abstractChartMetric_domain_eq (p : M) :
    (abstractChartMetric (E:=E) p).domain = (chartAt E p).target := by
  rw [abstractChartMetric_domain,extChartAt_target]
  change id ⁻¹' (chartAt E p).target ∩ Set.range id = _
  simp

namespace LocalBeltramiChart

variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

/-- The constructed Beltrami coordinates, composed with the ordinary atlas chart. -/
def manifoldChart : OpenPartialHomeomorph M E := (chartAt E p).trans C.chart

@[simp] theorem manifoldChart_apply (x : M) :
    C.manifoldChart x = C.chart (extChartAt 𝓘(ℝ,E) p x) := rfl

@[simp] theorem manifoldChart_symm_apply (y : E) :
    C.manifoldChart.symm y = (extChartAt 𝓘(ℝ,E) p).symm (C.chart.symm y) := rfl

theorem manifoldChart_source : C.manifoldChart.source =
    (chartAt E p).source ∩ (extChartAt 𝓘(ℝ,E) p) ⁻¹' C.chart.source := rfl

theorem manifoldChart_source_subset : C.manifoldChart.source ⊆ (chartAt E p).source :=
  fun _ hx => hx.1

@[simp] theorem manifoldChart_target : C.manifoldChart.target = C.chart.target := by
  ext y
  change (y ∈ C.chart.target ∧ C.chart.symm y ∈ (chartAt E p).target) ↔ _
  constructor
  · exact fun h => h.1
  · intro hy
    refine ⟨hy,?_⟩
    rw [←abstractChartMetric_domain_eq p]
    exact C.source_domain (C.chart.map_target hy)

theorem manifoldChart_base_mem : p ∈ C.manifoldChart.source :=
  ⟨mem_chart_source E p,C.base_mem⟩

@[simp] theorem manifoldChart_base_value : C.manifoldChart p = 0 := C.base_value

theorem manifoldChart_smooth :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ C.manifoldChart C.manifoldChart.source := by
  exact C.smooth.contMDiffOn.comp
    (contMDiffOn_chart.mono C.manifoldChart_source_subset) (fun _ hx => hx.2)

theorem manifoldChart_inverse_smooth :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ C.manifoldChart.symm C.manifoldChart.target := by
  apply (contMDiffOn_chart_symm (I:=𝓘(ℝ,E)) (x:=p)).comp
    (C.inverse_smooth.contMDiffOn.mono (by rw [C.manifoldChart_target]))
  intro y hy
  rw [←abstractChartMetric_domain_eq p]
  exact C.source_domain (C.chart.map_target (C.manifoldChart_target ▸ hy))

theorem manifoldChart_positive {x : M} (hx : x ∈ C.manifoldChart.source) :
    0 < beltramiDenominator κ (C.manifoldChart x) := C.positive _ hx.2

end LocalBeltramiChart
end OAI.Geometry.Nikodym
