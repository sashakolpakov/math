import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates

/-! # Tensor Transition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TensorTransition

noncomputable section

/-! Literal native transition units of tensor frames are the
products of the two actual regular transition units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem nativeTensorFrame_transition {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
    (e e' : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (d d' : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) U
      (RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame M N U e d) (RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame M N U e' d') =
        RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e e' * RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit N U d d' := by
  symm
  apply RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence.frameTransitionUnit_unique
  have h := RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame_scalar M N U e e' d d'
    (U.topIso.inv (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e e').val)
    (U.topIso.inv (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit N U d d').val)
    (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec M U e e') (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit_spec N U d d')
  exact h.trans (congrArg (fun s => (RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame M N U e' d').hom ≫
    SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection s) (map_mul U.topIso.inv.hom _ _).symm)

def nativeTensorLocalFrame {X : Scheme.{0}} {M N : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (d : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) : LineFrameAtlas.LocalLineFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) :=
  ⟨U, RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame M N U e d⟩

theorem nativeTensorLocalFrame_transition {X : Scheme.{0}} {M N : X.Modules} (U V W : X.Opens)
    (hU : W ≤ U) (hV : W ≤ V)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (e' : M.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme)
    (d : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (d' : N.restrict V.ι ≅ HilbertConstruction.Line.Bundles.structureModule V.toScheme) :
    (nativeTensorLocalFrame U e d).transition (nativeTensorLocalFrame V e' d') W hU hV =
      (⟨U, e⟩ : LineFrameAtlas.LocalLineFrame M).transition ⟨V, e'⟩ W hU hV *
        (⟨U, d⟩ : LineFrameAtlas.LocalLineFrame N).transition ⟨V, d'⟩ W hU hV := by
  have h₁ := LineFrameAtlas.LocalLineFrame.transition_native (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N)
    (nativeTensorLocalFrame U e d) (nativeTensorLocalFrame V e' d') W hU hV
  have h₂ := congrArg₂ (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) W)
    (RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame_restrict M N hU e d)
    (RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame_restrict M N hV e' d')
  have h₃ := nativeTensorFrame_transition M N W
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hU e) (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hV e')
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hU d) (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hV d')
  have h₄ := congrArg₂ (· * ·)
    (LineFrameAtlas.LocalLineFrame.transition_native M ⟨U, e⟩ ⟨V, e'⟩ W hU hV).symm
    (LineFrameAtlas.LocalLineFrame.transition_native N ⟨U, d⟩ ⟨V, d'⟩ W hU hV).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TensorTransition
