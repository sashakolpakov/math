import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameScalarRescaling
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameAtPoint

/-! # Frame Rescaling Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameRescalingPullback

noncomputable section

/-! Frame rescaling commutes with pullback and with transport to a
point, using the pulled-back unit of actual regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y Z : Scheme.{u}}

theorem structureScalarAutomorphism_pullback (a : X ⟶ Y) (c : Γ(Y, ⊤)ˣ) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).inv ≫ (Scheme.Modules.pullback a).map (FrameScalarRescaling.structureScalarAutomorphism c).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom =
      (FrameScalarRescaling.structureScalarAutomorphism (Units.map a.appTop.hom.toMonoidHom c)).hom := by
  apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X
  rw [AbelianModuli.HilbertConstruction.Scalar.BaseChange.structureModuleEndValue_baseChange, FrameScalarRescaling.structureScalarAutomorphism_hom_value,
    FrameScalarRescaling.structureScalarAutomorphism_hom_value]
  rfl

theorem pullbackFrame_rescale (a : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (c : Γ(Y, ⊤)ˣ) :
    FrameTransitionPullback.pullbackFrame a (FrameScalarRescaling.rescaleFrame e c) =
      FrameScalarRescaling.rescaleFrame (FrameTransitionPullback.pullbackFrame a e) (Units.map a.appTop.hom.toMonoidHom c) := by
  have h := structureScalarAutomorphism_pullback a c
  have h' := congrArg (fun k => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a).hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at h'
  apply Iso.ext
  simp only [FrameTransitionPullback.pullbackFrame, FrameScalarRescaling.rescaleFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [h']

theorem frameAtPoint_rescale (a : X ⟶ Y) (b : Y ⟶ Z) (p : X ⟶ Z) (h : a ≫ b = p)
    {M : Z.Modules} (e : (Scheme.Modules.pullback b).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (c : Γ(Y, ⊤)ˣ) :
    FrameAtPoint.frameAtPoint a b p h (FrameScalarRescaling.rescaleFrame e c) =
      FrameScalarRescaling.rescaleFrame (FrameAtPoint.frameAtPoint a b p h e) (Units.map a.appTop.hom.toMonoidHom c) := by
  unfold FrameAtPoint.frameAtPoint FramePullbackComposition.refineFrame
  rw [pullbackFrame_rescale]
  apply Iso.ext
  simp only [FrameScalarRescaling.rescaleFrame, Iso.trans_hom, Category.assoc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameRescalingPullback
