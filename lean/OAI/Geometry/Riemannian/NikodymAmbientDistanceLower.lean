import OAI.Geometry.Riemannian.NikodymAmbientDistancePath

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Filter Metric
open scoped ContDiff ENNReal NNReal Topology

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

local instance (x : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x) :=
  normedAddCommGroupTangentSpaceVectorSpace x
local instance (x : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x) :=
  normedSpaceTangentSpaceVectorSpace x

/-- On a sufficiently small neighborhood, the coordinate map is Lipschitz for the
ambient Riemannian distance. Paths leaving the coordinate neighborhood are included. -/
theorem exists_ambient_chart_lower (a : M) :
    ∃ K : ℝ≥0, 0 < K ∧ ∃ U : Set M, IsOpen U ∧ a ∈ U ∧
      U ⊆ (extChartAt I a).source ∧
      ∀ y ∈ U, ∀ z ∈ U,
        edist (extChartAt I a y) (extChartAt I a z) ≤ (K : ℝ≥0∞) * edist y z := by
  obtain ⟨C, hC, hder⟩ := eventually_enorm_mfderiv_extChartAt_lt I a
  have hder' : ∀ᶠ y in 𝓝 a, ‖modelMFDeriv (I := I) (extChartAt I a) y‖ₑ < C := by
    filter_upwards [hder] with y hy
    exact hy
  have hcoord : {y | edist (extChartAt I a y) (extChartAt I a a) < 1} ∈ 𝓝 a := by
    exact (continuousAt_extChartAt (I := I) a).preimage_mem_nhds
      (Metric.eball_mem_nhds (extChartAt I a a) (show (0 : ℝ≥0∞) < 1 by norm_num))
  have hall : (extChartAt I a).source ∩
      {y | ‖modelMFDeriv (I := I) (extChartAt I a) y‖ₑ < C} ∩
      {y | edist (extChartAt I a y) (extChartAt I a a) < 1} ∈ 𝓝 a :=
    inter_mem (inter_mem (extChartAt_source_mem_nhds a) hder') hcoord
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp hall
  obtain ⟨R, hR, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (2 : ℝ≥0∞)) (by norm_num) hε.ne'
  have hsmall' : 2 * (R : ℝ≥0∞) < ε := by simpa only [mul_comm] using hsmall
  have hR2 : (R : ℝ≥0∞) ≤ 2 * R := by
    rw [two_mul]
    exact le_self_add
  have hbig : Metric.eball a (2 * (R : ℝ≥0∞)) ⊆
      (extChartAt I a).source ∩
        {y | ‖modelMFDeriv (I := I) (extChartAt I a) y‖ₑ < C} ∩
        {y | edist (extChartAt I a y) (extChartAt I a a) < 1} :=
    fun y hy => hball (hy.trans hsmall')
  have hsub : Metric.eball a (R : ℝ≥0∞) ⊆ Metric.eball a (2 * (R : ℝ≥0∞)) :=
    fun y hy => hy.trans_le hR2
  let K : ℝ≥0 := C + 2 / R
  have hK : 0 < K := lt_of_lt_of_le hC le_self_add
  have hKC : C ≤ K := le_self_add
  have hKR : (2 : ℝ≥0) ≤ K * R := by
    dsimp [K]
    rw [add_mul, div_mul_cancel₀ _ hR.ne']
    exact le_add_self
  refine ⟨K, hK, Metric.eball a (R : ℝ≥0∞), isOpen_eball, ?_, ?_, ?_⟩
  · simp only [mem_eball, edist_self]
    exact_mod_cast hR
  · intro y hy
    exact (hbig (hsub hy)).1.1
  · intro y hy z hz
    have hd : edist (extChartAt I a y) (extChartAt I a z) ≤ (K : ℝ≥0∞) * R := by
      apply le_trans (edist_triangle _ (extChartAt I a a) _)
      have hy' : edist (extChartAt I a y) (extChartAt I a a) ≤ 1 :=
        le_of_lt (hbig (hsub hy)).2
      have hz' : edist (extChartAt I a z) (extChartAt I a a) ≤ 1 :=
        le_of_lt (hbig (hsub hz)).2
      rw [edist_comm (extChartAt I a a)]
      calc
        _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add hy' hz'
        _ = 2 := by norm_num
        _ ≤ (K : ℝ≥0∞) * R := by exact_mod_cast hKR
    apply image_edist_le_on_eball (I := I) hK hKC ?_ ?_ hy hd
    · apply contMDiffOn_extChartAt.mono
      intro w hw
      simpa only [extChartAt_source] using (hbig hw).1.1
    · intro w hw
      exact le_of_lt (hbig hw).1.2

end OAI.Geometry.Riemannian
