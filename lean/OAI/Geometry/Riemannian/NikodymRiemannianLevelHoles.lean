import OAI.Geometry.Nikodym.LocalCoordinateHoles
import OAI.Geometry.Riemannian.LengthSpace
import OAI.Geometry.Riemannian.NikodymAmbientDistance

noncomputable section
open Set Metric Filter Bundle Manifold
open scoped Topology ENNReal

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

/-- Positive distance levels for the ambient Riemannian metric are locally
porous in ordinary coordinates. All metric and path hypotheses are supplied
by the actual Riemannian structure. -/
theorem exists_distance_level_coordinate_holes (a : M) {A : Set M}
    (hA : A.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ x ∈ (extChartAt 𝓘(ℝ,E) a) '' ({z | infDist z A = δ} ∩ U),
          ∀ᶠ r : ℝ in 𝓝[>] 0,
            ∃ y : E, dist x y ≤ C*r ∧
              Disjoint ((extChartAt 𝓘(ℝ,E) a) '' ({z | infDist z A = δ} ∩ U))
                (closedBall y r) := by
  obtain ⟨K, L, hK, hL, U, hU, ha, hUs, hcomp⟩ :=
    exists_ambient_bilipschitz_chart (E := E) a
  have hK' : 0 < (K : ℝ) := hK
  have hL' : 0 < (L : ℝ) := hL
  have he (u : M) (hu : u ∈ U) (v : M) (hv : v ∈ U) :
      dist (extChartAt 𝓘(ℝ,E) a u) (extChartAt 𝓘(ℝ,E) a v) ≤ (K:ℝ) * dist u v := by
    have H := ENNReal.toReal_mono (by finiteness) (hcomp u hu v hv).1
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using H
  have hi (u : M) (hu : u ∈ U) (v : M) (hv : v ∈ U) :
      dist u v ≤ (L:ℝ) * dist (extChartAt 𝓘(ℝ,E) a u) (extChartAt 𝓘(ℝ,E) a v) := by
    have H := ENNReal.toReal_mono (by finiteness) (hcomp u hu v hv).2
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] using H
  have hX : OAI.Geometry.Nikodym.HasApproximateIntermediatePoints M := by
    intro x y s ε hs hsd hε
    exact exists_intermediate_dist (I := 𝓘(ℝ,E)) x y hs.le hsd.le hε
  refine ⟨U, hU, ha, hUs, 4*(K:ℝ)*(L:ℝ), by positivity, ?_⟩
  rintro z ⟨x, ⟨hx, hxU⟩, rfl⟩
  exact OAI.Geometry.Nikodym.local_coordinate_distance_level_small_holes hX hA
    (extChartAt 𝓘(ℝ,E) a) hL' he hi hx hδ (hU.mem_nhds hxU)

end OAI.Geometry.Riemannian
