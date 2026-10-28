import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEqualityBaseChange

/-! # Open Line Class Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenLineClassPullback.Construction

noncomputable section

/-! Equality of actual line classes on an open pulls back along every
morphism whose image lies in that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lineClass_eq_pullback_of_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hf : ∀ x : X, f x ∈ U) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass U.ι (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass U.ι (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hf x
  let g := IsOpenImmersion.lift U.ι f hr
  have H := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass g) h
  simpa only [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, g, IsOpenImmersion.lift_fac] using H

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenLineClassPullback.Construction
