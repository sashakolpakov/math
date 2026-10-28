import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineBundleIsoFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel

/-! # Pullback Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.PullbackDifference

noncomputable section

/-! Two original line-bundle pullbacks with equal reduction define
their actual tensor-difference bundle and a canonical element of the
infinitesimal Picard kernel. The difference is additive in three maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {Y : Scheme.{0}}
    (f g : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (h : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ f = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g)
    (L : HilbertConstruction.Line.Bundles.LineBundle Y)

def dualLinePullbackDifference : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left :=
  LineBundleIsoFrames.lineBundleDifference (L.pullback g) (L.pullback f)

def dualLinePullbackReductionIso :
    ((L.pullback g).pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).sheaf ≅
      ((L.pullback f).pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).sheaf :=
  (Scheme.Modules.pullbackComp (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left g).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h.symm).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left f).symm.app L.sheaf

def dualLinePullbackDifferenceFrame :
    ((dualLinePullbackDifference X f g L).pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).sheaf ≅
      HilbertConstruction.Line.Bundles.structureModule X.left :=
  (LineBundleIsoFrames.pulledLineBundleIsoFrameEquiv (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left (L.pullback g) (L.pullback f)
    (dualLinePullbackReductionIso X f g h L)).symm

def dualLinePullbackDifferenceKernel : ClassKernel.dualLineClassKernel X :=
  ClassKernel.dualLineClassKernelOfLine X (dualLinePullbackDifference X f g L) (dualLinePullbackDifferenceFrame X f g h L)

theorem dualLinePullbackDifferenceKernel_class :
    (dualLinePullbackDifferenceKernel X f g h L).val =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f) / HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback g) := rfl

theorem dualLinePullbackDifferenceKernel_comp (t : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (ht : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ t) :
    dualLinePullbackDifferenceKernel X f g h L * dualLinePullbackDifferenceKernel X g t ht L =
      dualLinePullbackDifferenceKernel X f t (h.trans ht) L := by
  apply Subtype.ext
  exact div_mul_div_cancel (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f))
    (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback g)) (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback t))

variable [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal
      (CategoryTheory.Limits.terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

def dualLinePullbackDifferenceClass : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X.left) 1 :=
  ClassKernel.dualLineKernelCohomology X (dualLinePullbackDifferenceKernel X f g h L)

theorem dualLinePullbackDifferenceClass_comp (t : (LieRanks.dualNumberTest ℂ ⊗ X).left ⟶ Y)
    (ht : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ g = (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ t) :
    dualLinePullbackDifferenceClass X f g h L + dualLinePullbackDifferenceClass X g t ht L =
      dualLinePullbackDifferenceClass X f t (h.trans ht) L := by
  exact (ClassKernel.dualLineKernelCohomology_mul X _ _).symm.trans
    (congrArg (ClassKernel.dualLineKernelCohomology X) (dualLinePullbackDifferenceKernel_comp X f g h L t ht))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.PullbackDifference
