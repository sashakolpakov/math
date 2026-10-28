import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.FrameCechMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationClass

/-! # Frame Class Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.FrameClassMorphism

noncomputable section

/-! The class of an actual pulled normalized frame atlas is exactly
the original native H1 pullback of the target atlas class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [LocallyOfFiniteType Y.hom] [IsReduced Y.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ Y).left))]
    (f : X ⟶ Y) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ Y).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y.left) {I J : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame Y L e₀)
    (hs : iSup (fun i => (s i).baseOpen Y L e₀) = ⊤)
    (V : J → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (r : J → I)
    (h : ∀ j, V j ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ (s (r j)).domain)
    (hV : ∀ j, IsAffineOpen (V j)) (hc : iSup (Dual.CechCoefficient.dualReducedCechCover X V) = ⊤)

theorem normalizedDualFrameClass_morphism :
    DualLine.DeformationClass.normalizedDualFrameClass X (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left)
      (DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀)
      (fun j => Dual.NormalizedFrameCover.NormalizedDualFrame.morphismPullback f L e₀ (s (r j)) (V j) (h j) (hV j)) hc =
      StructurePullback.nativeStructureH1Pullback f (DualLine.DeformationClass.normalizedDualFrameClass Y L e₀ s hs) := by
  let K := L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left
  let d := DualLine.KernelMorphism.dualMorphismReductionFrame f L e₀
  let t (j : J) := Dual.NormalizedFrameCover.NormalizedDualFrame.morphismPullback f L e₀ (s (r j)) (V j) (h j) (hV j)
  exact StructureCechRefinedPullback.nativeStructureCechClass_morphism f (fun i => (s i).baseOpen Y L e₀) (Dual.CechCoefficient.dualReducedCechCover X V) r
    (fun j => Dual.MorphismOpenReductionSquare.dualMorphismReducedOpen_le f (s (r j)).domain (V j) (h j)) hs hc
    (Dual.UnitCechCoefficients.dualUnitCechAdditive Y.left.sheaf.obj _
      (LineFrameDualCech.lineFrameDualCech Y (fun i => (s i).localFrame Y L e₀) (fun i => (s i).affine)))
    (Dual.UnitCechCoefficients.dualUnitCechAdditive X.left.sheaf.obj _
      (LineFrameDualCech.lineFrameDualCech X (fun j => (t j).localFrame X K d) hV))
    (Dual.UnitCechCoefficients.dualUnitCechAdditive_closed Y.left.sheaf.obj _ _ (Cech.normalizedDualFrames_cech Y L e₀ s)
      (LineFrameDualCech.lineFrameDualCech_cocycle Y (fun i => (s i).localFrame Y L e₀) (fun i => (s i).affine)))
    (Dual.UnitCechCoefficients.dualUnitCechAdditive_closed X.left.sheaf.obj _ _ (Cech.normalizedDualFrames_cech X K d t)
      (LineFrameDualCech.lineFrameDualCech_cocycle X (fun j => (t j).localFrame X K d) hV))
    (Dual.FrameCechMorphism.lineFrameDualCech_morphism f L.sheaf (fun i => (s i).domain) V r h (fun i => (s i).affine) hV
      (fun i => (s i).frame))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.FrameClassMorphism
