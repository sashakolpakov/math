import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.DifferentiatedEquation
import OAI.Analysis.PDE.Dirichlet.CoordinateTransport
import OAI.Analysis.PDE.Dirichlet.Translation

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

def spatialGradientRestriction (i : E →L[ℝ] W) :
    (W →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ E W ℝ).flip i

def spatialHessianRestriction (i : E →L[ℝ] W) :
    (W →L[ℝ] W →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E W (E →L[ℝ] ℝ)).flip i).comp
    ((ContinuousLinearMap.compL ℝ W (W →L[ℝ] ℝ) (E →L[ℝ] ℝ))
      (spatialGradientRestriction i))

@[simp] theorem spatialGradientRestriction_apply (i : E →L[ℝ] W)
    (a : W →L[ℝ] ℝ) (v : E) : spatialGradientRestriction i a v = a (i v) := rfl

@[simp] theorem spatialHessianRestriction_apply (i : E →L[ℝ] W)
    (A : W →L[ℝ] W →L[ℝ] ℝ) (v w : E) :
    spatialHessianRestriction i A v w = A (i v) (i w) := rfl

/-- Retain the parameter and spatial base points and restrict the genuine
gradient and Hessian to the spatial directions. W may already be a
Euclidean reindexing of the parameter-space product. -/
def parameterJetProjection (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W) :
    NonlinearJet W →L[ℝ] (Z × NonlinearJet E) :=
  let point : NonlinearJet W →L[ℝ] W :=
    (ContinuousLinearMap.fst ℝ W (W →L[ℝ] ℝ)).comp
      (ContinuousLinearMap.fst ℝ (W × (W →L[ℝ] ℝ)) (W →L[ℝ] W →L[ℝ] ℝ))
  let gradient : NonlinearJet W →L[ℝ] (W →L[ℝ] ℝ) :=
    (ContinuousLinearMap.snd ℝ W (W →L[ℝ] ℝ)).comp
      (ContinuousLinearMap.fst ℝ (W × (W →L[ℝ] ℝ)) (W →L[ℝ] W →L[ℝ] ℝ))
  let hessian : NonlinearJet W →L[ℝ] (W →L[ℝ] W →L[ℝ] ℝ) :=
    ContinuousLinearMap.snd ℝ (W × (W →L[ℝ] ℝ)) (W →L[ℝ] W →L[ℝ] ℝ)
  (p.comp point).prod (((q.comp point).prod
    ((spatialGradientRestriction i).comp gradient)).prod
      ((spatialHessianRestriction i).comp hessian))

@[simp] theorem parameterJetProjection_apply
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W) (j : NonlinearJet W) :
    parameterJetProjection p q i j =
      (p j.1.1, ((q j.1.1, spatialGradientRestriction i j.1.2),
        spatialHessianRestriction i j.2)) := rfl

theorem parameterJetProjection_normal
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    (ℓ : W →L[ℝ] ℝ) (k : E →L[ℝ] ℝ) (hk : ℓ.comp i = k) :
    parameterJetProjection p q i (0,ℓ.smulRight ℓ) = (0,(0,k.smulRight k)) := by
  have hg : spatialGradientRestriction i (0 : W →L[ℝ] ℝ) = 0 := map_zero _
  have hH : spatialHessianRestriction i (ℓ.smulRight ℓ) = k.smulRight k := by
    ext v w
    have hv : ℓ (i v) = k v := congrArg (fun L : E →L[ℝ] ℝ => L v) hk
    have hw : ℓ (i w) = k w := congrArg (fun L : E →L[ℝ] ℝ => L w) hk
    change ℓ (i v) * ℓ (i w) = k v * k w
    rw [hv,hw]
  simp only [parameterJetProjection_apply,Prod.fst_zero,Prod.snd_zero,map_zero,hg,hH]
  rfl

def parameterResidual (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    (F : Z × NonlinearJet E → ℝ) : NonlinearJet W → ℝ :=
  F ∘ parameterJetProjection p q i

theorem contDiff_parameterResidual
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    {F : Z × NonlinearJet E → ℝ} {r : ℕ∞ω} (hF : ContDiff ℝ r F) :
    ContDiff ℝ r (parameterResidual p q i F) :=
  hF.comp (parameterJetProjection p q i).contDiff

/-- Parameter enlargement preserves the actual normal principal symbol.
No ellipticity in the new parameter directions is needed. -/
theorem parameterResidual_normal_symbol
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    (F : Z × NonlinearJet E → ℝ) (j : NonlinearJet W)
    (ℓ : W →L[ℝ] ℝ) (k : E →L[ℝ] ℝ) (hk : ℓ.comp i = k)
    (hF : DifferentiableAt ℝ F (parameterJetProjection p q i j)) :
    fderiv ℝ (parameterResidual p q i F) j (0,ℓ.smulRight ℓ) =
      fderiv ℝ F (parameterJetProjection p q i j) (0,(0,k.smulRight k)) := by
  have hd := (hF.hasFDerivAt.comp j (parameterJetProjection p q i).hasFDerivAt).fderiv
  change fderiv ℝ (F ∘ parameterJetProjection p q i) j _ = _
  rw [hd,ContinuousLinearMap.comp_apply,parameterJetProjection_normal p q i ℓ k hk]

/-- On a parameter-space product, the lifted normal covector satisfies
the compatibility needed for preservation of the normal symbol. -/
theorem parameterResidual_product_normal_symbol
    (F : Z × NonlinearJet E → ℝ) (j : NonlinearJet (Z × E))
    (k : E →L[ℝ] ℝ)
    (hF : DifferentiableAt ℝ F
      (parameterJetProjection (ContinuousLinearMap.fst ℝ Z E)
        (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E) j)) :
    fderiv ℝ (parameterResidual (ContinuousLinearMap.fst ℝ Z E)
      (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E) F) j
      (0,(k.comp (ContinuousLinearMap.snd ℝ Z E)).smulRight
        (k.comp (ContinuousLinearMap.snd ℝ Z E))) =
    fderiv ℝ F (parameterJetProjection (ContinuousLinearMap.fst ℝ Z E)
      (ContinuousLinearMap.snd ℝ Z E) (ContinuousLinearMap.inr ℝ Z E) j)
      (0,(0,k.smulRight k)) := by
  apply parameterResidual_normal_symbol _ _ _ F j _ k _ hF
  ext v
  rfl

end OAI.Analysis.PDE.Dirichlet
