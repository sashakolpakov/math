import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Kernel Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelMorphism

noncomputable section

/-! An original scheme morphism pulls back the actual infinitesimal
line-class kernel, retaining its literal reduction square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem dualFamilyMorphism_reduction :
    RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X ≫ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f) =
      f ≫ RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction]

def dualMorphismReductionFrame (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ Y).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y.left) :
    (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj
      (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left).sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left :=
  RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left f.left
    (congrArg Over.Hom.left (dualFamilyMorphism_reduction f).symm) L.sheaf e

def dualLineKernelMorphismPullback : ClassKernel.dualLineClassKernel Y →* ClassKernel.dualLineClassKernel X where
  toFun x := ⟨HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left x.val, by
    have h := congrArg (fun q : X ⟶ LieRanks.dualNumberTest ℂ ⊗ Y => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q.left x.val)
      (dualFamilyMorphism_reduction f)
    have hl := HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
      (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left x.val
    have hr := HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp f.left (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left x.val
    exact hl.symm.trans (h.trans (hr.trans
      ((congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left) x.property).trans
        (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial f.left))))⟩
  map_one' := Subtype.ext (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial _)
  map_mul' x y := Subtype.ext (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_mul _ x.val y.val)

theorem dualLineKernelMorphismPullback_of_line (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ Y).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction Y).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y.left) :
    dualLineKernelMorphismPullback f (ClassKernel.dualLineClassKernelOfLine Y L e) =
      ClassKernel.dualLineClassKernelOfLine X (L.pullback (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left)
        (dualMorphismReductionFrame f L e) := Subtype.ext rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelMorphism
