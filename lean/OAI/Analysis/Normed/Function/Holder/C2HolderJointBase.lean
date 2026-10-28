import OAI.Analysis.Normed.Function.Holder.DerivativeBanach
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Joint differentiation of bounded continuous function families whose
spatial derivatives are controlled in the same bounded-function topology. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {Z E F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def zeroEvalCLM (K : Set E) (x : E) : (K →ᵇ F) →L[ℝ] F := by
  classical
  exact if hx : x ∈ K then BoundedContinuousFunction.evalCLM ℝ ⟨x,hx⟩ else 0

omit [NormedSpace ℝ E] in
theorem zeroEvalCLM_apply (K : Set E) (x : E) (f : K →ᵇ F) :
    zeroEvalCLM K x f = boundedZeroExtension f x := by
  classical
  by_cases hx : x ∈ K
  · simp only [zeroEvalCLM,dite_eq_left hx]
    exact (boundedZeroExtension_apply f hx).symm
  · simp [zeroEvalCLM,boundedZeroExtension,OAI.Analysis.PDE.Dirichlet.zeroExtend,hx]

omit [NormedSpace ℝ Z] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuousOn_joint_bcf {U : Set Z} {Ω K : Set E} (hΩK : Ω ⊆ K)
    (a : Z → K →ᵇ F) (ha : ContinuousOn a U) :
    ContinuousOn (fun p : Z × E => boundedZeroExtension (a p.1) p.2) (U ×ˢ Ω) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hz : Continuous (fun p : U ×ˢ Ω => (⟨p.val.1,p.property.1⟩ : U)) :=
    continuous_subtype_val.fst.subtype_mk _
  have hx : Continuous (fun p : U ×ˢ Ω => (⟨p.val.2,hΩK p.property.2⟩ : K)) :=
    continuous_subtype_val.snd.subtype_mk _
  have harest := continuousOn_iff_continuous_domRestrict.mp ha
  have he := continuous_eval.comp ((harest.comp hz).prodMk hx)
  convert he using 1
  funext p
  exact boundedZeroExtension_apply (a p.val.1) (hΩK p.property.2)

def jointBCFDerivative {K : Set E} (a : Z → K →ᵇ F)
    (b : Z → K →ᵇ (E →L[ℝ] F)) (p : Z × E) : Z × E →L[ℝ] F :=
  ((zeroEvalCLM K p.2).comp (fderiv ℝ a p.1)).coprod
    (boundedZeroExtension (b p.1) p.2)

theorem jointBCFDerivative_apply {K : Set E} (a : Z → K →ᵇ F)
    (b : Z → K →ᵇ (E →L[ℝ] F)) (p w : Z × E) :
    jointBCFDerivative a b p w =
      boundedZeroExtension (fderiv ℝ a p.1 w.1) p.2 +
        boundedZeroExtension (b p.1) p.2 w.2 := by
  simp only [jointBCFDerivative,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.comp_apply,zeroEvalCLM_apply]

theorem joint_bcf_contDiff_one [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]
    {U : Set Z} {Ω K : Set E} (hU : IsOpen U) (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (a : Z → K →ᵇ F) (b : Z → K →ᵇ (E →L[ℝ] F))
    (ha : ContDiffOn ℝ 1 a U) (hb : ContinuousOn b U)
    (hder : ∀ z ∈ U, ∀ x ∈ Ω,
      HasFDerivAt (boundedZeroExtension (a z)) (boundedZeroExtension (b z) x) x) :
    ContDiffOn ℝ 1 (fun p : Z × E => boundedZeroExtension (a p.1) p.2) (U ×ˢ Ω) ∧
      ∀ p ∈ U ×ˢ Ω, HasFDerivAt
        (fun p : Z × E => boundedZeroExtension (a p.1) p.2) (jointBCFDerivative a b p) p := by
  have ha' : ContinuousOn (fderiv ℝ a) U := ha.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hpart : ContinuousOn (fun p : Z × E => (zeroEvalCLM K p.2).comp (fderiv ℝ a p.1)) (U ×ˢ Ω) := by
    apply continuousOn_clm_apply.mpr
    intro w
    simpa only [ContinuousLinearMap.comp_apply,zeroEvalCLM_apply] using
      continuousOn_joint_bcf hΩK (fun z => fderiv ℝ a z w) (ha'.clm_apply continuousOn_const)
  have hb' := continuousOn_joint_bcf hΩK b hb
  have hd : ∀ p ∈ U ×ˢ Ω, HasFDerivAt
      (fun p : Z × E => boundedZeroExtension (a p.1) p.2) (jointBCFDerivative a b p) p := by
    intro p hp
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod
      (f := fun z x => boundedZeroExtension (a z) x)
      (f₁ := fun z x => (zeroEvalCLM K x).comp (fderiv ℝ a z))
      (f₂ := fun z x => boundedZeroExtension (b z) x)
    · filter_upwards [(hU.prod hΩ).mem_nhds hp] with q hq
      have hda : HasFDerivAt a (fderiv ℝ a q.1) q.1 :=
        (((ha q.1 hq.1).contDiffAt (hU.mem_nhds hq.1)).differentiableAt (by norm_num)).hasFDerivAt
      have h := (zeroEvalCLM K q.2).hasFDerivAt.comp q.1 hda
      simpa only [Function.comp_def,zeroEvalCLM_apply] using! h
    · filter_upwards [(hU.prod hΩ).mem_nhds hp] with q hq
      exact hder q.1 hq.1 q.2 hq.2
    · exact hpart.continuousAt ((hU.prod hΩ).mem_nhds hp)
    · exact hb'.continuousAt ((hU.prod hΩ).mem_nhds hp)
  refine ⟨?_,hd⟩
  change ContDiffOn ℝ (0+1) _ _
  rw [contDiffOn_succ_iff_fderiv_of_isOpen (hU.prod hΩ)]
  refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  have hc : ContinuousOn (jointBCFDerivative a b) (U ×ˢ Ω) := by
    apply continuousOn_clm_apply.mpr
    intro w
    simpa only [jointBCFDerivative_apply,Pi.add_apply] using!
      (continuousOn_joint_bcf hΩK (fun z => fderiv ℝ a z w.1)
        (ha'.clm_apply continuousOn_const)).add (hb'.clm_apply continuousOn_const)
  exact hc.congr (fun p hp => (hd p hp).fderiv)

end OAI.Analysis.Normed.Function.Holder
