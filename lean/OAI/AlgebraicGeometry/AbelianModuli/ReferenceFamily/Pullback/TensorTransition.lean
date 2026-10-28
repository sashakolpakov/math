import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.OpenFrameAgreement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TensorTransition

/-! # Tensor Transition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorTransition

noncomputable section

/-! The tensor frame made from actual pullback frames has the
product of their literal transition units on every common open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem algebraicPullbackTensorFrame_transition {X : Scheme.{0}} (M N : X.Modules) (U V W : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (e' : (Scheme.Modules.pullback V.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d' : (Scheme.Modules.pullback V.ι).obj N ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule V.toScheme) :
    (⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
      PullbackTensorFrame.algebraicPullbackTensorFrame U.ι M N e d⟩ : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).transition
      ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≪≫
        PullbackTensorFrame.algebraicPullbackTensorFrame V.ι M N e' d'⟩ W hU hV =
    (⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩ : LineFrameAtlas.LocalLineFrame M).transition
      ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ e'⟩ W hU hV *
    (⟨U, (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫ d⟩ : LineFrameAtlas.LocalLineFrame N).transition
      ⟨V, (Scheme.Modules.restrictFunctorIsoPullback V.ι).app N ≪≫ d'⟩ W hU hV := by
  have h := congrArg₂
    (fun (a : (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
      (b : (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme) =>
        (⟨U, a⟩ : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)).transition ⟨V, b⟩ W hU hV)
    (Tensor.OpenFrameAgreement.algebraicOpenFrame_pullback M N U e d) (Tensor.OpenFrameAgreement.algebraicOpenFrame_pullback M N V e' d')
  exact h.trans (Intrinsic.TensorTransition.nativeTensorLocalFrame_transition U V W hU hV
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e)
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫ e')
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫ d)
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N ≪≫ d'))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.TensorTransition
