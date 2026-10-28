import OAI.Geometry.Nikodym.SmoothMetric
import Mathlib.Analysis.CStarAlgebra.Matrix

open Set _root_.MeasureTheory Filter
open scoped RealInnerProductSpace ENNReal Topology Matrix.Norms.Elementwise ContDiff
noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {n : ℕ} (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n)))

/-- The coefficient matrix in the fixed Euclidean orthonormal coordinates. -/
def metricMatrix (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (g.coefficient x)

@[simp] theorem toEuclideanCLM_metricMatrix (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (g.metricMatrix x)=g.coefficient x :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _

theorem contDiffOn_metricMatrix : ContDiffOn ℝ ∞ g.metricMatrix g.domain := by
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.contDiff.comp_contDiffOn g.smooth

theorem metricMatrix_posDef {x : EuclideanSpace ℝ (Fin n)} (hx : x∈g.domain) :
    (g.metricMatrix x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSelfAdjoint]
    have hs : IsSelfAdjoint (g.coefficient x) :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (g.symmetric x hx)
    change star ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (g.coefficient x)) =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm (g.coefficient x)
    exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.map_star'
      (g.coefficient x)).symm.trans (congrArg
        (fun A => (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A) hs.star_eq)
  · intro v hv
    let u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hu : u≠0 := by
      intro h
      apply hv
      exact congrArg WithLp.ofLp h
    have hp := g.positive x hx u hu
    have he := Matrix.inner_toEuclideanCLM (g.metricMatrix x) u u
    rw [g.toEuclideanCLM_metricMatrix] at he
    rw [real_inner_comm,he] at hp
    simpa only [u,WithLp.ofLp_toLp,star_trivial] using hp

theorem metricMatrix_det_pos {x : EuclideanSpace ℝ (Fin n)} (hx : x∈g.domain) :
    0<(g.metricMatrix x).det := (g.metricMatrix_posDef hx).det_pos

/-- The genuine coordinate Riemannian volume density. -/
def volumeDensity (x : EuclideanSpace ℝ (Fin n)) : ℝ := Real.sqrt (g.metricMatrix x).det

theorem volumeDensity_nonneg (x : EuclideanSpace ℝ (Fin n)) : 0≤g.volumeDensity x :=
  Real.sqrt_nonneg _

theorem volumeDensity_pos {x : EuclideanSpace ℝ (Fin n)} (hx : x∈g.domain) :
    0<g.volumeDensity x := Real.sqrt_pos.mpr (g.metricMatrix_det_pos hx)

theorem continuousOn_volumeDensity : ContinuousOn g.volumeDensity g.domain := by
  exact (continuous_id.matrix_det.comp_continuousOn
    g.contDiffOn_metricMatrix.continuousOn).sqrt

/-- The measure is supported on the actual coordinate domain. Values of the
coefficient field outside that domain therefore have no geometric effect. -/
def coordinateVolume : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict g.domain).withDensity (fun x => ENNReal.ofReal (g.volumeDensity x))

theorem coordinateVolume_restrict {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (hSD : S⊆g.domain) :
    g.coordinateVolume.restrict S =
      (volume.restrict S).withDensity (fun x => ENNReal.ofReal (g.volumeDensity x)) := by
  rw [SmoothCoordinateMetric.coordinateVolume,restrict_withDensity hS,Measure.restrict_restrict hS,
    inter_eq_left.mpr hSD]

theorem coordinateVolume_restrict_bounds {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (hSD : S⊆g.domain) {c C : ℝ}
    (hc : ∀ x∈S,c≤g.volumeDensity x) (hC : ∀ x∈S,g.volumeDensity x≤C) :
    ENNReal.ofReal c • volume.restrict S ≤ g.coordinateVolume.restrict S ∧
      g.coordinateVolume.restrict S ≤ ENNReal.ofReal C • volume.restrict S := by
  rw [g.coordinateVolume_restrict hS hSD]
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with x hx
    exact ENNReal.ofReal_le_ofReal (hc x hx)
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with x hx
    exact ENNReal.ofReal_le_ofReal (hC x hx)

/-- Local two-sided Lebesgue comparison follows from the metric itself,
without a measure-comparison hypothesis. -/
theorem locally_comparable_coordinateVolume {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀∈g.domain) :
    ∃ r c C : ℝ,0<r ∧ 0<c ∧ 0<C ∧ Metric.closedBall x₀ r⊆g.domain ∧
      (∀ x∈Metric.closedBall x₀ r,c≤g.volumeDensity x ∧ g.volumeDensity x≤C) ∧
      ENNReal.ofReal c • volume.restrict (Metric.closedBall x₀ r) ≤
        g.coordinateVolume.restrict (Metric.closedBall x₀ r) ∧
      g.coordinateVolume.restrict (Metric.closedBall x₀ r) ≤
        ENNReal.ofReal C • volume.restrict (Metric.closedBall x₀ r) := by
  have hc := g.volumeDensity_pos hx₀
  have hcont : ContinuousAt g.volumeDensity x₀ :=
    (g.continuousOn_volumeDensity x₀ hx₀).continuousAt (g.isOpen_domain.mem_nhds hx₀)
  have hn : ∀ᶠ x in 𝓝 x₀,x∈g.domain ∧
      g.volumeDensity x₀/2<g.volumeDensity x ∧ g.volumeDensity x<2*g.volumeDensity x₀ := by
    filter_upwards [g.isOpen_domain.mem_nhds hx₀,
      hcont.eventually (Ioo_mem_nhds
        (show g.volumeDensity x₀/2<g.volumeDensity x₀ by linarith)
        (show g.volumeDensity x₀<2*g.volumeDensity x₀ by linarith))] with x hx hh
    exact ⟨hx,hh⟩
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp hn
  have hinc : Metric.closedBall x₀ (s/2)⊆Metric.ball x₀ s :=
    Metric.closedBall_subset_ball (by linarith)
  have hSD : Metric.closedBall x₀ (s/2)⊆g.domain := fun x hx => (hball (hinc hx)).1
  have hb : ∀ x∈Metric.closedBall x₀ (s/2),
      g.volumeDensity x₀/2≤g.volumeDensity x ∧ g.volumeDensity x≤2*g.volumeDensity x₀ :=
    fun x hx => ⟨(hball (hinc hx)).2.1.le,(hball (hinc hx)).2.2.le⟩
  have hvol := g.coordinateVolume_restrict_bounds Metric.isClosed_closedBall.measurableSet hSD
    (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)
  exact ⟨s/2,g.volumeDensity x₀/2,2*g.volumeDensity x₀,half_pos hs,half_pos hc,
    mul_pos (by norm_num) hc,hSD,hb,hvol⟩

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
