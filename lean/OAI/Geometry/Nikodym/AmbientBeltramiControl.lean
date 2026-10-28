import OAI.Geometry.Nikodym.Abstract.Metric
import OAI.Geometry.Riemannian.NikodymAmbientDistance
import OAI.Geometry.Nikodym.Chart.Localization

noncomputable section
open Set Bundle Manifold Filter Metric
open scoped ContDiff Topology ENNReal

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [PseudoEMetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

variable (p : M) {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

def ambientBeltramiForward (x : M) : E := C.chart (extChartAt 𝓘(ℝ,E) p x)

def ambientBeltramiInverse (y : E) : M :=
  (extChartAt 𝓘(ℝ,E) p).symm (C.chart.symm y)

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem ambientBeltramiInverse_center : ambientBeltramiInverse p C 0 = p := by
  rw [ambientBeltramiInverse,C.inverse_center]
  exact (extChartAt 𝓘(ℝ,E) p).left_inv (mem_extChartAt_source p)

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem ambientBeltramiForward_inverse {y : E} (hy : y ∈ C.chart.target) :
    ambientBeltramiForward p C (ambientBeltramiInverse p C y) = y := by
  have ht := C.source_domain (C.chart.map_target hy)
  dsimp only [ambientBeltramiForward,ambientBeltramiInverse]
  rw [(extChartAt 𝓘(ℝ,E) p).right_inv ht,C.chart.right_inv hy]

/-- The actual constant-curvature chart has uniform two-sided Lipschitz
bounds for ambient Riemannian distance on a compactly contained patch.
The comparison includes ambient paths which leave the coordinate domain. -/
theorem exists_ambientBeltrami_controlled_ball :
    ∃ (r : ℝ) (K L : NNReal), 0 < r ∧ 1 ≤ K ∧ 1 ≤ L ∧
      closedBall (0 : E) (2*r) ⊆ C.chart.target ∧
      (∀ y ∈ closedBall (0 : E) (2*r), |κ| * ‖y‖^2 ≤ 1/2) ∧
      LipschitzOnWith K (ambientBeltramiForward p C)
        (ambientBeltramiInverse p C '' closedBall (0 : E) (2*r)) ∧
      LipschitzOnWith L (ambientBeltramiInverse p C) (closedBall (0 : E) (2*r)) ∧
      IsCompact (ambientBeltramiInverse p C '' closedBall (0 : E) (2*r)) := by
  let A := extChartAt 𝓘(ℝ,E) p
  obtain ⟨K₀,L₀,hK₀,hL₀,U,hU,hpU,hUA,hUL⟩ :=
    OAI.Geometry.Riemannian.exists_ambient_bilipschitz_chart (E:=E) p
  have hAc : ContinuousAt A.symm (A p) :=
    (continuousOn_extChartAt_symm p _ (A.map_source (mem_extChartAt_source p))).continuousAt
      (extChartAt_target_mem_nhds p)
  have hW : A.target ∩ A.symm ⁻¹' U ∈ 𝓝 (A p) := by
    apply inter_mem (extChartAt_target_mem_nhds p)
    apply hAc.preimage_mem_nhds
    simpa only [A,A.left_inv (mem_extChartAt_source p)] using hU.mem_nhds hpU
  obtain ⟨s,hs,hst,hsU⟩ := C.exists_target_ball_inside hW
  obtain ⟨t,K₁,L₁,ht,hK₁,hL₁,htt,hsmall,hCf,hCi,hcompact,hsource⟩ :=
    C.exists_small_biLipschitz_target_ball
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  have hrs : closedBall (0 : E) (2*r) ⊆ closedBall 0 (2*s) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hrt : closedBall (0 : E) (2*r) ⊆ closedBall 0 (2*t) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
  have hyU (y : E) (hy : y ∈ closedBall (0 : E) (2*r)) :
      C.chart.symm y ∈ A.target ∩ A.symm ⁻¹' U := hsU ⟨y,hrs hy,rfl⟩
  have hInv : LipschitzOnWith (L₀*L₁) (ambientBeltramiInverse p C)
      (closedBall (0 : E) (2*r)) := by
    intro y hy z hz
    have h₀ := (hUL _ (hyU y hy).2 _ (hyU z hz).2).2
    change edist (A.symm (C.chart.symm y)) (A.symm (C.chart.symm z)) ≤ _
    rw [A.right_inv (hyU y hy).1,A.right_inv (hyU z hz).1] at h₀
    calc
      _ ≤ (L₀ : ℝ≥0∞) * edist (C.chart.symm y) (C.chart.symm z) := h₀
      _ ≤ (L₀ : ℝ≥0∞) * ((L₁ : ℝ≥0∞) * edist y z) :=
        mul_le_mul' le_rfl (hCi (hrt hy) (hrt hz))
      _ = _ := by simp only [ENNReal.coe_mul,mul_assoc]
  have hFor : LipschitzOnWith (K₁*K₀) (ambientBeltramiForward p C)
      (ambientBeltramiInverse p C '' closedBall (0 : E) (2*r)) := by
    rintro x ⟨y,hy,rfl⟩ z ⟨w,hw,rfl⟩
    have h₀ := (hUL _ (hyU y hy).2 _ (hyU w hw).2).1
    rw [A.right_inv (hyU y hy).1,A.right_inv (hyU w hw).1] at h₀
    rw [ambientBeltramiForward_inverse p C (htt (hrt hy)),
      ambientBeltramiForward_inverse p C (htt (hrt hw))]
    have h₁ := hCf (mem_image_of_mem C.chart.symm (hrt hy))
      (mem_image_of_mem C.chart.symm (hrt hw))
    rw [C.chart.right_inv (htt (hrt hy)),C.chart.right_inv (htt (hrt hw))] at h₁
    calc
      _ ≤ (K₁ : ℝ≥0∞) * edist (C.chart.symm y) (C.chart.symm w) := h₁
      _ ≤ (K₁ : ℝ≥0∞) * ((K₀ : ℝ≥0∞) *
          edist (ambientBeltramiInverse p C y) (ambientBeltramiInverse p C w)) :=
        mul_le_mul' le_rfl h₀
      _ = _ := by simp only [ENNReal.coe_mul,mul_assoc]
  exact ⟨r,max (K₁*K₀) 1,max (L₀*L₁) 1,hr,le_max_right _ _,le_max_right _ _,
    hrt.trans htt,fun y hy => hsmall y (hrt hy),
    hFor.weaken (le_max_left _ _),hInv.weaken (le_max_left _ _),
    (isCompact_closedBall (0 : E) (2*r)).image_of_continuousOn hInv.continuousOn⟩

end OAI.Geometry.Nikodym
