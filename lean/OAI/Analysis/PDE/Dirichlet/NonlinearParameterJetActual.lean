import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJet

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {Z E W : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Restricting the actual product two-jet gives exactly the two-jet of
the spatial slice, not an independent formal field. -/
theorem parameterJetProjection_product_twoJet
    {f : Z × E → ℝ} (hf : ContDiff ℝ 2 f) (z : Z) (x : E) :
    parameterJetProjection (ContinuousLinearMap.fst ℝ Z E)
      (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E)
      (nonlinearTwoJet f (z,x)) = (z,nonlinearTwoJet (fun y => f (z,y)) x) := by
  have hD : fderiv ℝ (fun y => f (z,y)) x =
      (fderiv ℝ f (z,x)).comp (ContinuousLinearMap.inr ℝ Z E) :=
    ((hf.differentiable (by norm_num) (z,x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right z x)).fderiv
  have hH (v w : E) : fderiv ℝ (fderiv ℝ (fun y => f (z,y))) x v w =
      fderiv ℝ (fderiv ℝ f) (z,x) (0,v) (0,w) := by
    have h := second_fderiv_comp_between (fun a : Z × E => f ((z,0)+a))
      (hf.comp (contDiff_const.add contDiff_id)) (ContinuousLinearMap.inr ℝ Z E) x v w
    rw [second_fderiv_translation] at h
    simpa only [Function.comp_def,ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk,zero_add,add_zero] using h
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext
      · rfl
      · change spatialGradientRestriction (ContinuousLinearMap.inr ℝ Z E)
          (fderiv ℝ f (z,x)) = fderiv ℝ (fun y => f (z,y)) x
        exact hD.symm
    · ext v w
      exact (hH v w).symm

theorem parameterResidual_product_twoJet
    (F : Z × NonlinearJet E → ℝ) {f : Z × E → ℝ}
    (hf : ContDiff ℝ 2 f) (z : Z) (x : E) :
    parameterResidual (ContinuousLinearMap.fst ℝ Z E)
      (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E) F
      (nonlinearTwoJet f (z,x)) = F (z,nonlinearTwoJet (fun y => f (z,y)) x) := by
  exact congrArg F (parameterJetProjection_product_twoJet hf z x)

/-- The enlarged normal derivative is the spatial residual derivative
with its external parameter held fixed. -/
theorem parameterResidual_normal_symbol_slice
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    (F : Z × NonlinearJet E → ℝ) (j : NonlinearJet W)
    (ℓ : W →L[ℝ] ℝ) (k : E →L[ℝ] ℝ) (hk : ℓ.comp i = k)
    (hF : DifferentiableAt ℝ F (parameterJetProjection p q i j)) :
    fderiv ℝ (parameterResidual p q i F) j (0,ℓ.smulRight ℓ) =
      fderiv ℝ (fun a => F ((parameterJetProjection p q i j).1,a))
        (parameterJetProjection p q i j).2 (0,k.smulRight k) := by
  have hd := (hF.hasFDerivAt.comp (parameterJetProjection p q i j).2
    (hasFDerivAt_prodMk_right (parameterJetProjection p q i j).1
      (parameterJetProjection p q i j).2)).fderiv
  rw [parameterResidual_normal_symbol p q i F j ℓ k hk hF]
  exact (congrArg (fun A : NonlinearJet E →L[ℝ] ℝ => A (0,k.smulRight k)) hd).symm

end OAI.Analysis.PDE.Dirichlet
