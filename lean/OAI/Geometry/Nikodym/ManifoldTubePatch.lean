import OAI.Geometry.Nikodym.ManifoldPatch
import OAI.Geometry.Nikodym.Chart.Neighborhood

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold Metric
open scoped ContDiff

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,Space n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
    (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContinuousRiemannianBundle (Space n) (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Space n) M]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
  (extChartAt 𝓘(ℝ,Space n) p p))

/-- All metric and margin data for a fixed local Nikodym patch. Every field
is constructed below from the actual Riemannian metric and curvature chart. -/
structure ManifoldTubePatch where
  radius : ℝ
  radius_pos : 0 < radius
  K : NNReal
  L : NNReal
  one_le_K : 1 ≤ K
  one_le_L : 1 ≤ L
  target : closedBall (0 : Space n) (2*radius) ⊆ C.chart.target
  small : ∀ y ∈ closedBall (0 : Space n) (2*radius), |κ| * ‖y‖^2 ≤ 1/2
  forward_lipschitz : LipschitzOnWith K C.manifoldForward (C.manifoldPatch (ball 0 (2*radius)))
  inverse_lipschitz : LipschitzOnWith L C.manifoldInverse (closedBall 0 (2*radius))
  compact_core : IsCompact (C.manifoldPatch (closedBall 0 radius))
  base_mem : p ∈ C.manifoldPatch (ball 0 radius)
  width : ℝ
  width_pos : 0 < width
  width_le_radius : width ≤ radius
  scaled_width : (K : ℝ)*width ≤ 1
  ambient_margin : ∀ {I : Set M}, I ⊆ C.manifoldPatch (closedBall 0 radius) →
    ∀ {δ : ℝ}, δ ≤ width → metricTube δ I ⊆ C.manifoldPatch (ball 0 (2*radius))

omit [MeasurableSpace M] [BorelSpace M] in
theorem nonempty_manifoldTubePatch : Nonempty (LocalBeltramiChart.ManifoldTubePatch C) := by
  obtain ⟨r,K,L,hr,hK,hL,ht,hs,hf,hi,hcompact,hopen,hbase⟩ :=
    C.exists_manifold_controlled_patch
  have hcore : C.manifoldPatch (closedBall (0 : Space n) r) ⊆
      C.manifoldPatch (ball 0 (2*r)) :=
    C.manifoldPatch_mono (closedBall_subset_ball (by linarith))
  obtain ⟨ε,hε,hmargin⟩ := exists_uniform_metricTube_margin hcompact hopen hcore
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  let δ₀ := min ε (min r (1/(K : ℝ)))
  have hδ₀ : 0 < δ₀ := lt_min hε (lt_min hr (one_div_pos.mpr hKpos))
  have hδK : δ₀ ≤ 1/(K : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  have hscaled : (K : ℝ)*δ₀ ≤ 1 := by
    calc
      (K : ℝ)*δ₀ ≤ (K : ℝ)*(1/(K : ℝ)) := mul_le_mul_of_nonneg_left hδK hKpos.le
      _ = 1 := by field_simp
  exact ⟨⟨r,hr,K,L,hK,hL,ht,hs,hf,hi,hcompact,hbase,δ₀,hδ₀,
    (min_le_right _ _).trans (min_le_left _ _),hscaled,
    fun {_} hI {_} hδ => hmargin hI (hδ.trans (min_le_left _ _))⟩⟩

namespace ManifoldTubePatch

variable {C}

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem inner_tube_margin (P : LocalBeltramiChart.ManifoldTubePatch C) {δ : ℝ} (hδ : δ ≤ P.width)
    {v c : Space n} (hseg : OAI.MeasureTheory.Kakeya.unitSegment v c ⊆ closedBall 0 P.radius) :
    OAI.MeasureTheory.Kakeya.tube (δ/(P.L : ℝ)) v c ⊆ ball 0 (2*P.radius) := by
  apply tube_subset_double_ball _ hseg
  have hLpos : (0 : ℝ) < P.L := lt_of_lt_of_le zero_lt_one P.one_le_L
  apply (div_le_iff₀ hLpos).mpr
  have hδr := hδ.trans P.width_le_radius
  calc
    δ ≤ P.radius := hδr
    _ ≤ P.radius * (P.L : ℝ) := by
      nlinarith [show (1 : ℝ) ≤ P.L from P.one_le_L,P.radius_pos]

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem scaled_width_le (P : LocalBeltramiChart.ManifoldTubePatch C) {δ : ℝ} (hδ : δ ≤ P.width) :
    (P.K : ℝ)*δ ≤ 1 :=
  (mul_le_mul_of_nonneg_left hδ P.K.coe_nonneg).trans P.scaled_width

end ManifoldTubePatch
end OAI.Geometry.Nikodym.LocalBeltramiChart
