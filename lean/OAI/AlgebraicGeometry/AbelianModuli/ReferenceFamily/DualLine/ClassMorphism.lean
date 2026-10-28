import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.FrameClassMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MorphismFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel

/-! # Class Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassMorphism

noncomputable section

/-! Original scheme pullback on infinitesimal line bundles agrees
with the original native structure-sheaf H1 pullback. All compatible
normalized affine frames and cover refinements are constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [LocallyOfFiniteType Y.hom] [IsReduced Y.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ Y).left))]
    (f : X ⟶ Y)

theorem dualLineDeformationClass_morphism (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ Y).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y.left) :
    DeformationClass.dualLineDeformationClass X (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left)
      (KernelMorphism.dualMorphismReductionFrame f L e₀) = StructurePullback.nativeStructureH1Pullback f (DeformationClass.dualLineDeformationClass Y L e₀) := by
  let s := Dual.NormalizedFrameCover.normalizedDualFrameAt Y L e₀
  let K := L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left
  let d := KernelMorphism.dualMorphismReductionFrame f L e₀
  have hc := Dual.MorphismFrameCover.dualMorphismCoverFrame_covers f L e₀ s (Dual.NormalizedFrameCover.normalizedDualFrameCover_base Y L e₀)
  have he := FrameIndependence.dualLineDeformationClass_eq_frames X K d (Dual.MorphismFrameCover.dualMorphismCoverFrame f L e₀ s) hc
  exact he.trans (NormalizedDual.FrameClassMorphism.normalizedDualFrameClass_morphism f L e₀ s (Dual.NormalizedFrameCover.normalizedDualFrameCover_base Y L e₀)
    (fun i : Dual.MorphismFrameCover.DualMorphismFrameIndex f L e₀ s => i.chart.1) (fun i => i.target)
    (fun i => i.target_le) (fun i => i.chart.2) hc)

theorem dualLineKernelCohomology_morphism (q : ClassKernel.dualLineClassKernel Y) :
    ClassKernel.dualLineKernelCohomology X (KernelMorphism.dualLineKernelMorphismPullback f q) =
      StructurePullback.nativeStructureH1Pullback f (ClassKernel.dualLineKernelCohomology Y q) := by
  let L := ClassKernel.dualLineKernelRepresentative Y q
  let e := ClassKernel.dualLineKernelFrame Y q
  have h : HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left) =
      (KernelMorphism.dualLineKernelMorphismPullback f q).val :=
    congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left)
      (ClassKernel.dualLineKernelRepresentative_class Y q)
  exact (ClassKernel.dualLineKernelCohomology_rep X (KernelMorphism.dualLineKernelMorphismPullback f q)
    (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left) (KernelMorphism.dualMorphismReductionFrame f L e) h).trans
      (dualLineDeformationClass_morphism f L e)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassMorphism
