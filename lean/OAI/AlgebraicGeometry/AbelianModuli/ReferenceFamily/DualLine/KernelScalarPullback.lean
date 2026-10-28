import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Scalars

/-! # Kernel Scalar Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelScalarPullback

noncomputable section

/-! Native scalar maps act on the actual reduction kernel by
pullback of the original line-bundle isomorphism classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

def fixedReductionPullbackFrame {X Y : Scheme.{0}} (r : X ⟶ Y) (q : Y ⟶ Y) (hq : r ≫ q = r)
    {M : Y.Modules} (e : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) :
    (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback q).obj M) ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X :=
  (Scheme.Modules.pullbackComp r q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫ e

def dualLineKernelPullback (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (q : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (hq : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ q = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left) :
    ClassKernel.dualLineClassKernel X →* ClassKernel.dualLineClassKernel X where
  toFun x := ⟨HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q x.val,
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left q x.val).symm.trans
      ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f x.val) hq).trans x.property)⟩
  map_one' := Subtype.ext (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial q)
  map_mul' x y := Subtype.ext (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_mul q x.val y.val)

def dualLineKernelScalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (c : ℂ) : ClassKernel.dualLineClassKernel X →* ClassKernel.dualLineClassKernel X :=
  dualLineKernelPullback X (Dual.Scalars.dualFamilyScalar X c).left
    (congrArg (fun f : X ⟶ LieRanks.dualNumberTest ℂ ⊗ X => f.left) (Dual.Scalars.dualFamilyScalar_reduction X c))

theorem dualLineKernelPullback_of_line (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (q : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (hq : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ q = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left)
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) :
    dualLineKernelPullback X q hq (ClassKernel.dualLineClassKernelOfLine X L e) =
      ClassKernel.dualLineClassKernelOfLine X (L.pullback q)
        (fixedReductionPullbackFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left q hq e) := Subtype.ext rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelScalarPullback
