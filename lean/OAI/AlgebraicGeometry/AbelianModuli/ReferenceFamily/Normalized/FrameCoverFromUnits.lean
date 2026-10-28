import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentGlobalFrameGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.LineFramePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.OpenFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover

/-! # Frame Cover From Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.FrameCoverFromUnits

noncomputable section

/-! Local line frames whose original transition units reduce to
one admit a common global reduction frame. The same actual local
frames then give normalized dual frames, with their cover retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

theorem exists_common_reduction_frame {X Y : Scheme.{0}} (r : X ⟶ Y) {M : Y.Modules}
    {I : Type} (s : I → LineFrameAtlas.LocalLineFrame M) (hs : iSup (fun i => (s i).domain) = ⊤)
    (hu : ∀ i j, Units.map (r.app ((s i).domain ⊓ (s j).domain)).hom.toMonoidHom
      ((s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right) = 1) :
    ∃ e : (Scheme.Modules.pullback r).obj M ≅ HilbertConstruction.Line.Bundles.structureModule X,
      ∀ i, RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M (s i).domain (s i).frame = Global.FrameOverComparison.globalOpenFrame e (r ⁻¹ᵁ (s i).domain) := by
  obtain ⟨e, he⟩ := CoherentGlobalFrameGluing.exists_global_frame_agreeing (fun i => (s i).pullbackBy r)
    (Local.LineFramePullback.localLineFrame_pullback_cover r s hs) (fun i j =>
      ((s i).pullbackBy_transition r (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right).trans (hu i j))
  exact ⟨e, fun i => (he i).symm⟩

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X.left)

def normalizedDualFrameOfOpen (s : LineFrameAtlas.LocalLineFrame L.sheaf) (ha : IsAffineOpen s.domain)
    (hs : RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left L.sheaf s.domain s.frame =
      Global.FrameOverComparison.globalOpenFrame e ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ s.domain)) :
    Dual.NormalizedFrameCover.NormalizedDualFrame X L e where
  domain := s.domain
  affine := ha
  frame := (Scheme.Modules.restrictFunctorIsoPullback s.domain.ι).symm.app L.sheaf ≪≫ s.frame
  reduces := OpenFrameCriterion.reducedOpenFrame_of_open (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left e s.domain s.frame hs

theorem normalizedDualFrameOfOpen_localFrame (s : LineFrameAtlas.LocalLineFrame L.sheaf) (ha : IsAffineOpen s.domain)
    (hs : RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left L.sheaf s.domain s.frame =
      Global.FrameOverComparison.globalOpenFrame e ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ s.domain)) :
    (normalizedDualFrameOfOpen X L e s ha hs).localFrame X L e = s := by
  change (⟨s.domain, (Scheme.Modules.restrictFunctorIsoPullback s.domain.ι).app L.sheaf ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback s.domain.ι).symm.app L.sheaf ≪≫ s.frame⟩ : LineFrameAtlas.LocalLineFrame L.sheaf) = s
  exact congrArg (fun f => (⟨s.domain, f⟩ : LineFrameAtlas.LocalLineFrame L.sheaf)) (Iso.self_symm_id_assoc _ _)

omit e in
theorem exists_normalizedDualFrames_of_reduced_units {I : Type} (s : I → LineFrameAtlas.LocalLineFrame L.sheaf)
    (ha : ∀ i, IsAffineOpen (s i).domain) (hs : iSup (fun i => (s i).domain) = ⊤)
    (hu : ∀ i j, Units.map ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app ((s i).domain ⊓ (s j).domain)).hom.toMonoidHom
      ((s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right) = 1) :
    ∃ (e : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X.left)
      (t : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e),
      (∀ i, (t i).localFrame X L e = s i) ∧ iSup (fun i => (t i).baseOpen X L e) = ⊤ := by
  obtain ⟨e, he⟩ := exists_common_reduction_frame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left s hs hu
  let t := fun i => normalizedDualFrameOfOpen X L e (s i) (ha i) (he i)
  exact ⟨e, t, fun i => normalizedDualFrameOfOpen_localFrame X L e (s i) (ha i) (he i),
    Local.LineFramePullback.localLineFrame_pullback_cover (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left s hs⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.FrameCoverFromUnits
