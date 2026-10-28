import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PullbackTensorFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.FrameRestriction

/-! # Tensor Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.TensorFrames

noncomputable section

/-! Actual normalized frames for the original tensor line bundle
are constructed on the common affine opens of its two factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (d₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj K.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

def dualTensorReductionFrame :
    (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj (L.tensor K).sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left :=
  PullbackTensorFrame.algebraicPullbackTensorFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left L.sheaf K.sheaf e₀ d₀

def normalizedDualTensorFrameOn (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : IsAffineOpen U)
    (e : (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj K.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (he : Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X U) e = Dual.NormalizedLocalFrames.prescribedReducedLocalFrame X e₀ U)
    (hd : Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X U) d = Dual.NormalizedLocalFrames.prescribedReducedLocalFrame X d₀ U) :
    Dual.NormalizedFrameCover.NormalizedDualFrame X (L.tensor K) (dualTensorReductionFrame X L K e₀ d₀) where
  domain := U
  affine := hU
  frame := PullbackTensorFrame.algebraicPullbackTensorFrame U.ι L.sheaf K.sheaf e d
  reduces := PullbackTensorFrame.reducedOpenFrame_algebraic_tensor (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left U e₀ d₀ e d he hd

def normalizedDualTensorFramePair
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) (b : Dual.NormalizedFrameCover.NormalizedDualFrame X K d₀) :
    Dual.NormalizedFrameCover.NormalizedDualFrame X (L.tensor K) (dualTensorReductionFrame X L K e₀ d₀) :=
  let hU : IsAffineOpen (a.domain ⊓ b.domain) := a.affine.inf b.affine
  let a' := a.restrict X L e₀ (a.domain ⊓ b.domain) hU inf_le_left
  let b' := b.restrict X K d₀ (a.domain ⊓ b.domain) hU inf_le_right
  normalizedDualTensorFrameOn X L K e₀ d₀ (a.domain ⊓ b.domain) hU a'.frame b'.frame a'.reduces b'.reduces

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.TensorFrames
