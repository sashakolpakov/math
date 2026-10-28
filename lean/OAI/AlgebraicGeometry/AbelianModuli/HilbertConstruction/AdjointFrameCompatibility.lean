import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointFrameImages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleFrameLocal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorChanges

/-! # Adjoint Frame Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointFrameCompatibility

noncomputable section

/-! Images of the original local frames under a map into a direct image satisfy precisely the pulled-back frame transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U) (f : X ⟶ Y)
variable {N : X.Modules} (β : OpenFrame.ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj N)

theorem adjointFrameGenerator_scalar (W : Y.Opens) (i : ι) (hi : W ≤ U i) (r : Γ(Y, W)) :
    β.app W (OpenFrame.SectionGenerators.openFrameGenerator D W i hi r) =
      @SMul.smul Γ(X, f ⁻¹ᵁ W) Γ(N, f ⁻¹ᵁ W) inferInstance
        (f.app W r) (β.app W (OpenFrame.SectionGenerators.openFrameGenerator D W i hi 1)) :=
  (congrArg (β.app W) (OpenFrame.GeneratorNaturality.openFrameGenerator_smul_one D W i hi r).symm).trans
    (β.app_smul r (OpenFrame.SectionGenerators.openFrameGenerator D W i hi 1))

theorem adjointFrameImage_change (V : X.Opens) (i j : ι)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) :
    AdjointFrameImages.adjointFrameImage D f β V j hj =
      ((D.pullback f).value V i j hi hj).val • AdjointFrameImages.adjointFrameImage D f β V i hi := by
  let W := U i ⊓ U j
  have wi : W ≤ U i := inf_le_left
  have wj : W ≤ U j := inf_le_right
  have hV : V ≤ f ⁻¹ᵁ W := le_inf hi hj
  let t := (D.value W i j wi wj).val
  have hg : OpenFrame.SectionGenerators.openFrameGenerator D W j wj 1 = OpenFrame.SectionGenerators.openFrameGenerator D W i wi t :=
    (OpenFrame.GeneratorChanges.openFrameGenerator_change D W i j wi wj 1).symm.trans
      (congrArg (OpenFrame.SectionGenerators.openFrameGenerator D W i wi) (mul_one t))
  have hb := (congrArg (β.app W) hg).trans (adjointFrameGenerator_scalar D f β W i wi t)
  have hr := (congrArg (N.presheaf.map (homOfLE hV).op) hb).trans
    (Scheme.Modules.map_smul N (homOfLE hV) (f.app W t) (β.app W (OpenFrame.SectionGenerators.openFrameGenerator D W i wi 1)))
  have hiV := AdjointFrameImages.adjointFrameImage_refine D f β V i hi W wi hV
  have hjV := AdjointFrameImages.adjointFrameImage_refine D f β V j hj W wj hV
  exact hjV.trans (hr.trans (congrArg (fun a : Γ(N, V) =>
    ((D.pullback f).value V i j hi hj).val • a) hiV.symm))

def adjointCompatibleFrameImages : CompatibleFrameLocal.CompatibleFrameImages (D.pullback f) N where
  value := AdjointFrameImages.adjointFrameImage D f β
  restrict := AdjointFrameImages.adjointFrameImage_restrict D f β
  change := adjointFrameImage_change D f β

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointFrameCompatibility
