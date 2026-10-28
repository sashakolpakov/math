import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.FrameCoverFromUnits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ReductionFrameIndependence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.FrameIndependence

/-! # Class From Open Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassFromOpenFrames

noncomputable section

/-! The native Picard deformation class can be computed from the
original affine open frames whenever their transition units reduce
to one. The global reduction frame is constructed from those frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem dualLineDeformationClass_eq_openFrames
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    {I : Type} (s : I → LineFrameAtlas.LocalLineFrame L.sheaf)
    (ha : ∀ i, IsAffineOpen (s i).domain) (hs : iSup (fun i => (s i).domain) = ⊤)
    (hu : ∀ i j, Units.map ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app ((s i).domain ⊓ (s j).domain)).hom.toMonoidHom
      ((s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right) = 1) :
    ∃ (hcover : iSup (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) = ⊤)
      (hn : Dual.UnitCechCoefficients.DualUnitCechNormalized X.left.sheaf.obj
        (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain)) (LineFrameDualCech.lineFrameDualCech X s ha)),
      DeformationClass.dualLineDeformationClass X L e₀ =
        Regular.DualUnitClass.regularDualUnitClass X.left (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain))
          hcover (LineFrameDualCech.lineFrameDualCech X s ha) hn (LineFrameDualCech.lineFrameDualCech_cocycle X s ha) := by
  obtain ⟨e, t, ht, hc⟩ := Normalized.FrameCoverFromUnits.exists_normalizedDualFrames_of_reduced_units X L s ha hs hu
  have heq : (fun i => (t i).localFrame X L e) = s := funext ht
  subst s
  exact ⟨hc, NormalizedDual.Cech.normalizedDualFrames_cech X L e t,
    (ReductionFrameIndependence.dualLineDeformationClass_frame_independent X L e e₀).trans
      (FrameIndependence.dualLineDeformationClass_eq_frames X L e t hc)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassFromOpenFrames
