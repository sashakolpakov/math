import OAI.Geometry.Riemannian.NikodymAmbientDistanceUpper

noncomputable section
open Set Bundle Manifold
open scoped ContDiff ENNReal NNReal Topology

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

/-- Ordinary coordinates on a boundaryless Riemannian manifold are locally bi-Lipschitz
for the ambient distance. Neither side uses the intrinsic distance of a restricted chart. -/
theorem exists_ambient_bilipschitz_chart (a : M) :
    ∃ K L : ℝ≥0, 0 < K ∧ 0 < L ∧ ∃ U : Set M,
      IsOpen U ∧ a ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      ∀ y ∈ U, ∀ z ∈ U,
        edist (extChartAt 𝓘(ℝ,E) a y) (extChartAt 𝓘(ℝ,E) a z) ≤
          (K : ℝ≥0∞) * edist y z ∧
        edist y z ≤ (L : ℝ≥0∞) *
          edist (extChartAt 𝓘(ℝ,E) a y) (extChartAt 𝓘(ℝ,E) a z) := by
  obtain ⟨K, hK, U, hU, haU, hUs, hlo⟩ := exists_ambient_chart_lower (I := 𝓘(ℝ,E)) a
  obtain ⟨L, hL, V, hV, haV, hVs, hup⟩ := exists_ambient_chart_upper (E := E) a
  refine ⟨K, L, hK, hL, U ∩ V, hU.inter hV, ⟨haU, haV⟩,
    fun y hy => hUs hy.1, ?_⟩
  intro y hy z hz
  exact ⟨hlo y hy.1 z hz.1, hup y hy.2 z hz.2⟩

/-- Subtype formulation, ready for metric and Hausdorff-dimension transport. -/
theorem exists_bilipschitz_chart_restriction (a : M) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      ∃ K L : ℝ≥0, 0 < K ∧ 0 < L ∧
        LipschitzWith K (fun y : U => extChartAt 𝓘(ℝ,E) a y) ∧
        AntilipschitzWith L (fun y : U => extChartAt 𝓘(ℝ,E) a y) := by
  obtain ⟨K, L, hK, hL, U, hU, haU, hUs, h⟩ := exists_ambient_bilipschitz_chart (E := E) a
  refine ⟨U, hU, haU, hUs, K, L, hK, hL, ?_, ?_⟩
  · intro y z
    exact (h y y.property z z.property).1
  · intro y z
    exact (h y y.property z z.property).2

end OAI.Geometry.Riemannian
