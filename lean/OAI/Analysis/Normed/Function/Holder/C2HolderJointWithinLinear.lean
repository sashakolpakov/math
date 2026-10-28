import OAI.Analysis.Normed.Function.Holder.C2HolderJointWithinBase
import OAI.Analysis.Normed.Function.Holder.C2HolderJointLinear

noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {Z E F H : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

local instance withinFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance withinFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance withinSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance withinSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

theorem joint_linear_bcf_contDiff_one_within {U : Set Z} {S K : Set E}
    (hU : IsOpen U) (hSK : S ⊆ K)
    (L₀ : H →L[ℝ] (K →ᵇ F)) (L₁ : H →L[ℝ] (K →ᵇ (E →L[ℝ] F)))
    (hjet : ∀ v : H, ∀ x ∈ S, HasFDerivWithinAt
      (boundedZeroExtension (L₀ v)) (boundedZeroExtension (L₁ v) x) S x)
    (u : Z → H) (hu : ContDiffOn ℝ 1 u U) :
    ContDiffOn ℝ 1 (fun p : Z × E => boundedZeroExtension (L₀ (u p.1)) p.2) (U ×ˢ S) ∧
      ∀ p ∈ U ×ˢ S, HasFDerivWithinAt
        (fun p : Z × E => boundedZeroExtension (L₀ (u p.1)) p.2)
        (jointJetDerivative L₀ L₁ u p) (U ×ˢ S) p := by
  have ha := L₀.contDiff.comp_contDiffOn hu
  refine ⟨joint_bcf_contDiff_one_within hU hSK _ _ ha
    (L₁.continuous.comp_continuousOn hu.continuousOn)
    (fun z hz x hx => hjet (u z) x hx),?_⟩
  intro p hp
  have he : fderiv ℝ (fun z => L₀ (u z)) p.1 = L₀.comp (fderiv ℝ u p.1) :=
    (L₀.hasFDerivAt.comp p.1
      (((hu p.1 hp.1).contDiffAt (hU.mem_nhds hp.1)).differentiableAt
        (by norm_num)).hasFDerivAt).fderiv
  have hd := hasFDerivWithinAt_joint_bcf hU hSK
    (fun z => L₀ (u z)) (fun z => L₁ (u z)) ha p hp (hjet (u p.1) p.2 hp.2)
  simpa only [jointBCFDerivative,he,jointJetDerivative] using hd

theorem joint_linear_bcf_contDiff_two_within {U : Set Z} {S K : Set E}
    (hU : IsOpen U) (hSK : S ⊆ K)
    (L₀ : H →L[ℝ] (K →ᵇ F)) (L₁ : H →L[ℝ] (K →ᵇ (E →L[ℝ] F)))
    (L₂ : H →L[ℝ] (K →ᵇ (E →L[ℝ] E →L[ℝ] F)))
    (hjet₀ : ∀ v : H, ∀ x ∈ S, HasFDerivWithinAt
      (boundedZeroExtension (L₀ v)) (boundedZeroExtension (L₁ v) x) S x)
    (hjet₁ : ∀ v : H, ∀ x ∈ S, HasFDerivWithinAt
      (boundedZeroExtension (L₁ v)) (boundedZeroExtension (L₂ v) x) S x)
    (u : Z → H) (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (fun p : Z × E => boundedZeroExtension (L₀ (u p.1)) p.2) (U ×ˢ S) := by
  have hu₁ : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  apply OAI.Analysis.PDE.Dirichlet.contDiffOn_succ_of_derivative_field 1
    (G := jointJetDerivative L₀ L₁ u)
  · apply contDiffOn_clm_apply.mpr
    intro w
    have hparam : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z w.1) U :=
      (hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
    have hA := (joint_linear_bcf_contDiff_one_within hU hSK L₀ L₁ hjet₀
      (fun z => fderiv ℝ u z w.1) hparam).1
    have hB := (joint_linear_bcf_contDiff_one_within hU hSK L₁ L₂ hjet₁ u hu₁).1
    have hsum : ContDiffOn ℝ 1 (fun p : Z × E =>
        boundedZeroExtension (L₀ (fderiv ℝ u p.1 w.1)) p.2 +
        boundedZeroExtension (L₁ (u p.1)) p.2 w.2) (U ×ˢ S) :=
      hA.add (hB.clm_apply contDiffOn_const)
    simpa only [Nat.cast_one,jointJetDerivative_apply] using! hsum
  · exact (joint_linear_bcf_contDiff_one_within hU hSK L₀ L₁ hjet₀ u hu₁).2

end OAI.Analysis.Normed.Function.Holder
