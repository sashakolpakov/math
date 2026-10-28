import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCechReindex

/-! # Frame Independence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.FrameIndependence

noncomputable section

/-! The actual line-family class is independent of every choice of
normalized affine frame and cover. The union of two normalized atlases
is itself a normalized atlas, and each original atlas reindexes it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

theorem normalizedDualFrameClass_reindex {I J : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤) (r : J → I)
    (hr : iSup (fun j => (s (r j)).baseOpen X L e₀) = ⊤) :
    DeformationClass.normalizedDualFrameClass X L e₀ (s ∘ r) hr = DeformationClass.normalizedDualFrameClass X L e₀ s hs :=
  Dual.UnitCechReindex.dualUnitCechClass_reindex X.left.sheaf (fun i => (s i).baseOpen X L e₀) r hs hr
    (LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))
    (NormalizedDual.Cech.normalizedDualFrames_cech X L e₀ s)
    (LineFrameDualCech.lineFrameDualCech_cocycle X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine))

theorem normalizedDualFrameClass_independent {I J : Type}
    (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤)
    (t : J → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) (ht : iSup (fun j => (t j).baseOpen X L e₀) = ⊤) :
    DeformationClass.normalizedDualFrameClass X L e₀ s hs = DeformationClass.normalizedDualFrameClass X L e₀ t ht := by
  let v : I ⊕ J → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀ := Sum.elim s t
  have hv : iSup (fun k => (v k).baseOpen X L e₀) = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ iSup (fun i => (s i).baseOpen X L e₀) := by rw [hs]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨Sum.inl i, hi⟩
  exact (normalizedDualFrameClass_reindex X L e₀ v hv Sum.inl hs).trans
    (normalizedDualFrameClass_reindex X L e₀ v hv Sum.inr ht).symm

theorem dualLineDeformationClass_eq_frames {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤) :
    DeformationClass.dualLineDeformationClass X L e₀ = DeformationClass.normalizedDualFrameClass X L e₀ s hs :=
  normalizedDualFrameClass_independent X L e₀ (Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀)
    (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀) s hs

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.FrameIndependence
