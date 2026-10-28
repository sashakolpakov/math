import OAI.Analysis.Normed.Function.Holder.C2HolderJointBase

/-! Joint C² evaluation for a normed linear space with two genuine bounded spatial jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {Z E F H : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

local instance firstJetGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance firstJetSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance secondJetGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance secondJetSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

def jointJetDerivative {K : Set E} (L₀ : H →L[ℝ] (K →ᵇ F))
    (L₁ : H →L[ℝ] (K →ᵇ (E →L[ℝ] F))) (u : Z → H) (p : Z × E) :
    Z × E →L[ℝ] F :=
  ((zeroEvalCLM K p.2).comp (L₀.comp (fderiv ℝ u p.1))).coprod
    (boundedZeroExtension (L₁ (u p.1)) p.2)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] in
theorem jointJetDerivative_apply {K : Set E} (L₀ : H →L[ℝ] (K →ᵇ F))
    (L₁ : H →L[ℝ] (K →ᵇ (E →L[ℝ] F))) (u : Z → H) (p w : Z × E) :
    jointJetDerivative L₀ L₁ u p w =
      boundedZeroExtension (L₀ (fderiv ℝ u p.1 w.1)) p.2 +
        boundedZeroExtension (L₁ (u p.1)) p.2 w.2 := by
  simp only [jointJetDerivative,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.comp_apply,zeroEvalCLM_apply]

theorem joint_linear_bcf_contDiff_one {U : Set Z} {Ω K : Set E}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (L₀ : H →L[ℝ] (K →ᵇ F)) (L₁ : H →L[ℝ] (K →ᵇ (E →L[ℝ] F)))
    (hjet : ∀ v : H, ∀ x ∈ Ω, HasFDerivAt
      (boundedZeroExtension (L₀ v)) (boundedZeroExtension (L₁ v) x) x)
    (u : Z → H) (hu : ContDiffOn ℝ 1 u U) :
    ContDiffOn ℝ 1 (fun p : Z × E => boundedZeroExtension (L₀ (u p.1)) p.2) (U ×ˢ Ω) ∧
      ∀ p ∈ U ×ˢ Ω, HasFDerivAt
        (fun p : Z × E => boundedZeroExtension (L₀ (u p.1)) p.2) (jointJetDerivative L₀ L₁ u p) p := by
  have h := joint_bcf_contDiff_one hU hΩ hΩK
    (fun z => L₀ (u z)) (fun z => L₁ (u z))
    (L₀.contDiff.comp_contDiffOn hu) (L₁.continuous.comp_continuousOn hu.continuousOn)
    (fun z hz x hx => hjet (u z) x hx)
  refine ⟨h.1,?_⟩
  intro p hp
  have hu' := ((hu p.1 hp.1).contDiffAt (hU.mem_nhds hp.1)).differentiableAt (by norm_num)
  have he : fderiv ℝ (fun z => L₀ (u z)) p.1 = L₀.comp (fderiv ℝ u p.1) :=
    (L₀.hasFDerivAt.comp p.1 hu'.hasFDerivAt).fderiv
  have hd := h.2 p hp
  simpa only [jointBCFDerivative,he,jointJetDerivative] using hd

theorem joint_linear_bcf_contDiff_two {U : Set Z} {Ω K : Set E}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (L₀ : H →L[ℝ] (K →ᵇ F)) (L₁ : H →L[ℝ] (K →ᵇ (E →L[ℝ] F)))
    (L₂ : H →L[ℝ] (K →ᵇ (E →L[ℝ] E →L[ℝ] F)))
    (hjet₀ : ∀ v : H, ∀ x ∈ Ω, HasFDerivAt
      (boundedZeroExtension (L₀ v)) (boundedZeroExtension (L₁ v) x) x)
    (hjet₁ : ∀ v : H, ∀ x ∈ Ω, HasFDerivAt
      (boundedZeroExtension (L₁ v)) (boundedZeroExtension (L₂ v) x) x)
    (u : Z → H) (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (fun p : Z × E => boundedZeroExtension (L₀ (u p.1)) p.2) (U ×ˢ Ω) := by
  have hu₁ : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  have hd := (joint_linear_bcf_contDiff_one hU hΩ hΩK L₀ L₁ hjet₀ u hu₁).2
  change ContDiffOn ℝ (1+1) _ _
  apply contDiffOn_succ_of_fderiv_apply
  · exact fun p hp => (hd p hp).differentiableAt.differentiableWithinAt
  · norm_num
  · intro w
    have hparam : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z w.1) U :=
      (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
    have hA := (joint_linear_bcf_contDiff_one hU hΩ hΩK L₀ L₁ hjet₀
      (fun z => fderiv ℝ u z w.1) hparam).1
    have hB := (joint_linear_bcf_contDiff_one hU hΩ hΩK L₁ L₂ hjet₁ u hu₁).1
    have hsum : ContDiffOn ℝ 1 (fun p : Z × E =>
        boundedZeroExtension (L₀ (fderiv ℝ u p.1 w.1)) p.2 +
        boundedZeroExtension (L₁ (u p.1)) p.2 w.2) (U ×ˢ Ω) :=
      hA.add (hB.clm_apply contDiffOn_const)
    apply hsum.congr
    intro p hp
    rw [(hd p hp).hasFDerivWithinAt.fderivWithin ((hU.prod hΩ).uniqueDiffOn p hp),
      jointJetDerivative_apply]

end OAI.Analysis.Normed.Function.Holder
