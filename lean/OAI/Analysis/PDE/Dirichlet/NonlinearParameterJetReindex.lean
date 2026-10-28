import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetActual
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

/-! Exact reindexing of a parameter-dependent nonlinear equation and its normal symbol. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Dirichlet

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {Z E W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def reindexParameterProjection (e : W ≃L[ℝ] Z × E) : W →L[ℝ] Z :=
  (ContinuousLinearMap.fst ℝ Z E).comp e.toContinuousLinearMap

def reindexSpatialProjection (e : W ≃L[ℝ] Z × E) : W →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ Z E).comp e.toContinuousLinearMap

def reindexSpatialInclusion (e : W ≃L[ℝ] Z × E) : E →L[ℝ] W :=
  e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Z E)

@[simp] theorem reindexParameterProjection_apply (e : W ≃L[ℝ] Z × E) (w : W) :
    reindexParameterProjection e w = (e w).1 := rfl

@[simp] theorem reindexSpatialProjection_apply (e : W ≃L[ℝ] Z × E) (w : W) :
    reindexSpatialProjection e w = (e w).2 := rfl

@[simp] theorem reindexSpatialInclusion_apply (e : W ≃L[ℝ] Z × E) (v : E) :
    e (reindexSpatialInclusion e v) = (0,v) := by
  exact e.apply_symm_apply (0,v)

theorem reindexSpatialProjection_comp_inclusion (e : W ≃L[ℝ] Z × E) :
    (reindexSpatialProjection e).comp (reindexSpatialInclusion e) =
      ContinuousLinearMap.id ℝ E := by
  ext v
  change (e (reindexSpatialInclusion e v)).2 = v
  rw [reindexSpatialInclusion_apply]

theorem reindexNormal_comp_inclusion (e : W ≃L[ℝ] Z × E) (k : E →L[ℝ] ℝ) :
    (k.comp (reindexSpatialProjection e)).comp (reindexSpatialInclusion e) = k := by
  ext v
  change k ((e (reindexSpatialInclusion e v)).2) = k v
  rw [reindexSpatialInclusion_apply]

theorem parameterJetProjection_reindex_ambient
    (e : W ≃L[ℝ] Z × E) {f : Z × E → ℝ} (hf : ContDiff ℝ 2 f) (w : W) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) (nonlinearTwoJet (fun y => f (e y)) w) =
    parameterJetProjection (ContinuousLinearMap.fst ℝ Z E)
      (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E)
      (nonlinearTwoJet f (e w)) := by
  have hD : fderiv ℝ (fun y => f (e y)) w =
      (fderiv ℝ f (e w)).comp e.toContinuousLinearMap :=
    ((hf.differentiable (by norm_num) (e w)).hasFDerivAt.comp w
      e.toContinuousLinearMap.hasFDerivAt).fderiv
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · ext v
        change fderiv ℝ (fun y => f (e y)) w (reindexSpatialInclusion e v) =
          fderiv ℝ f (e w) (0,v)
        rw [hD,ContinuousLinearMap.comp_apply]
        change fderiv ℝ f (e w) (e (reindexSpatialInclusion e v)) = _
        rw [reindexSpatialInclusion_apply]
    · ext v v'
      change fderiv ℝ (fderiv ℝ (fun y => f (e y))) w
        (reindexSpatialInclusion e v) (reindexSpatialInclusion e v') =
          fderiv ℝ (fderiv ℝ f) (e w) (0,v) (0,v')
      have h := second_fderiv_comp_between f hf e.toContinuousLinearMap w
        (reindexSpatialInclusion e v) (reindexSpatialInclusion e v')
      simpa only [Function.comp_def,ContinuousLinearEquiv.coe_coe,
        reindexSpatialInclusion_apply] using h

theorem parameterJetProjection_reindex_twoJet
    (e : W ≃L[ℝ] Z × E) {f : Z × E → ℝ} (hf : ContDiff ℝ 2 f) (w : W) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) (nonlinearTwoJet (fun y => f (e y)) w) =
        ((e w).1,nonlinearTwoJet (fun y => f ((e w).1,y)) (e w).2) := by
  rw [parameterJetProjection_reindex_ambient e hf]
  exact parameterJetProjection_product_twoJet hf (e w).1 (e w).2

theorem parameterResidual_reindex_twoJet
    (e : W ≃L[ℝ] Z × E) (F : Z × NonlinearJet E → ℝ)
    {f : Z × E → ℝ} (hf : ContDiff ℝ 2 f) (w : W) :
    parameterResidual (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) F (nonlinearTwoJet (fun y => f (e y)) w) =
        F ((e w).1,nonlinearTwoJet (fun y => f ((e w).1,y)) (e w).2) :=
  congrArg F (parameterJetProjection_reindex_twoJet e hf w)

theorem parameterResidual_reindex_normal_symbol
    (e : W ≃L[ℝ] Z × E) (F : Z × NonlinearJet E → ℝ)
    (j : NonlinearJet W) (k : E →L[ℝ] ℝ)
    (hF : DifferentiableAt ℝ F (parameterJetProjection (reindexParameterProjection e)
      (reindexSpatialProjection e) (reindexSpatialInclusion e) j)) :
    fderiv ℝ (parameterResidual (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) F) j
      (0,(k.comp (reindexSpatialProjection e)).smulRight
        (k.comp (reindexSpatialProjection e))) =
      fderiv ℝ (fun a => F ((reindexParameterProjection e) j.1.1,a))
        (parameterJetProjection (reindexParameterProjection e)
          (reindexSpatialProjection e) (reindexSpatialInclusion e) j).2
        (0,k.smulRight k) :=
  parameterResidual_normal_symbol_slice _ _ _ F j _ k
    (reindexNormal_comp_inclusion e k) hF

theorem nonlinearTwoJet_congr_germ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} {x : X} (h : f =ᶠ[𝓝 x] g) :
    nonlinearTwoJet f x = nonlinearTwoJet g x := by
  change ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x) =
    ((x,fderiv ℝ g x),fderiv ℝ (fderiv ℝ g) x)
  rw [h.fderiv_eq,(h.fderiv (𝕜 := ℝ)).fderiv_eq]

section Local
variable [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]

/-- The exact spatial-jet identity is local: no global regularity of the
joint family away from the point is required. -/
theorem parameterJetProjection_reindex_twoJet_at
    (e : W ≃L[ℝ] Z × E) {f : Z × E → ℝ} (w : W)
    (hf : ContDiffAt ℝ 2 f (e w)) :
    parameterJetProjection (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) (nonlinearTwoJet (fun y => f (e y)) w) =
        ((e w).1,nonlinearTwoJet (fun y => f ((e w).1,y)) (e w).2) := by
  obtain ⟨g,hg,hgf⟩ := exists_contDiff_extension_near_point hf
  have heq : (fun y => g (e y)) =ᶠ[𝓝 w] (fun y => f (e y)) :=
    hgf.comp_tendsto (e.continuous.tendsto w)
  have hs : (fun y => g ((e w).1,y)) =ᶠ[𝓝 (e w).2]
      (fun y => f ((e w).1,y)) :=
    hgf.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  rw [← nonlinearTwoJet_congr_germ heq,parameterJetProjection_reindex_twoJet e hg,
    nonlinearTwoJet_congr_germ hs]

theorem parameterResidual_reindex_twoJet_at
    (e : W ≃L[ℝ] Z × E) (F : Z × NonlinearJet E → ℝ)
    {f : Z × E → ℝ} (w : W) (hf : ContDiffAt ℝ 2 f (e w)) :
    parameterResidual (reindexParameterProjection e) (reindexSpatialProjection e)
      (reindexSpatialInclusion e) F (nonlinearTwoJet (fun y => f (e y)) w) =
        F ((e w).1,nonlinearTwoJet (fun y => f ((e w).1,y)) (e w).2) :=
  congrArg F (parameterJetProjection_reindex_twoJet_at e w hf)

theorem parameterResidual_reindex_equation_on
    (e : W ≃L[ℝ] Z × E) (F : Z × NonlinearJet E → ℝ)
    {f : Z × E → ℝ} {S : Set (Z × E)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ 2 f S)
    (heq : ∀ z x, (z,x) ∈ S → F (z,nonlinearTwoJet (fun y => f (z,y)) x) = 0) :
    ∀ w ∈ e ⁻¹' S, parameterResidual (reindexParameterProjection e)
      (reindexSpatialProjection e) (reindexSpatialInclusion e) F
        (nonlinearTwoJet (fun y => f (e y)) w) = 0 := by
  intro w hw
  rw [parameterResidual_reindex_twoJet_at e F w ((hf (e w) hw).contDiffAt (hS.mem_nhds hw))]
  exact heq (e w).1 (e w).2 hw

end Local

end OAI.Analysis.PDE.Dirichlet
