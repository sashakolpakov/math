import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.IsoInvariance
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrameReduction

/-! # Reduction Frame Independence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ReductionFrameIndependence

noncomputable section

/-! The algebraic deformation class is independent of its chosen
global reduction frame and invariant under arbitrary actual line-sheaf isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem dualLineDeformationClass_frame_independent
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e d : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) :
    DeformationClass.dualLineDeformationClass X L d = DeformationClass.dualLineDeformationClass X L e := by
  let p := (CategoryTheory.CartesianMonoidalCategory.snd (LieRanks.dualNumberTest ℂ) X).left
  let q := SplitFrameReduction.splitReductionFrameAut (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left p e d
  have h := SplitFrameReduction.splitReductionFrameAut_reduces (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left p
    (congrArg (fun f : X ⟶ X => f.left) (Dual.ReductionOpens.dualBaseChangeReduction_projection X)) e d
  exact (congrArg (DeformationClass.dualLineDeformationClass X L) h).symm.trans (IsoInvariance.dualLineDeformationClass_iso X L L e q)

theorem dualLineDeformationClass_of_iso
    (L K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (d : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj K.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (q : K.sheaf ≅ L.sheaf) : DeformationClass.dualLineDeformationClass X K d = DeformationClass.dualLineDeformationClass X L e :=
  (dualLineDeformationClass_frame_independent X K
    ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e) d).trans
      (IsoInvariance.dualLineDeformationClass_iso X L K e q)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ReductionFrameIndependence
