import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.ReductionFramePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Scalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover

/-! # Scalar Frame Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual

noncomputable section

/-! Native scalar pullback gives constructed normalized frames on
the same actual affine family opens, retaining all reduction comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem ScalarFramePullback.dualOpenScalar_reduction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (c : ℂ) :
    DualOpen.Product.dualOpenReduction X U ≫ DualOpen.Scalars.dualOpenScalar X U c = DualOpen.Product.dualOpenReduction X U := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, DualOpen.Scalars.dualOpenScalar_ι, ← Category.assoc, DualOpen.Product.dualOpenReduction_ι, Category.assoc]
  have h := congrArg (fun f : X ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left) (Scalars.dualFamilyScalar_reduction X c)
  exact congrArg (fun f => ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι ≫ f) h

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (c : ℂ)

def ScalarFramePullback.dualScalarReductionFrame :
    (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj
      (L.pullback (Scalars.dualFamilyScalar X c).left).sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left :=
  DualLine.KernelScalarPullback.fixedReductionPullbackFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left (Scalars.dualFamilyScalar X c).left
    (congrArg (fun f : X ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left) (Scalars.dualFamilyScalar_reduction X c)) e₀

def NormalizedFrameCover.NormalizedDualFrame.scalarPullback (a : NormalizedFrameCover.NormalizedDualFrame X L e₀) :
    NormalizedFrameCover.NormalizedDualFrame X (L.pullback (Scalars.dualFamilyScalar X c).left) (ScalarFramePullback.dualScalarReductionFrame X L e₀ c) where
  domain := a.domain
  affine := a.affine
  frame := RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (Scalars.dualFamilyScalar X c).left a.domain.ι a.domain.ι
    (DualOpen.Scalars.dualOpenScalar X a.domain c) (DualOpen.Scalars.dualOpenScalar_ι X a.domain c) L.sheaf a.frame
  reduces := Fixed.ReductionFramePullback.fixedReductionFrame_square_normalized (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left (Scalars.dualFamilyScalar X c).left
    (congrArg (fun f : X ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left) (Scalars.dualFamilyScalar_reduction X c)) a.domain
    (DualOpen.Scalars.dualOpenScalar X a.domain c) (DualOpen.Scalars.dualOpenScalar_ι X a.domain c) (ScalarFramePullback.dualOpenScalar_reduction X a.domain c)
    e₀ a.frame a.reduces

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual
