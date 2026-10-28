import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TransitionGaugeGluing

/-! # Deformation Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationTriviality

noncomputable section

/-! Vanishing of the constructed algebraic H1 class gives an actual
global trivialization of the original line bundle on the nonreduced family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

omit [LocallyOfFiniteType X.hom] [IsReduced X.left]
  [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))] in
theorem normalizedDualFrames_cover_family {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤) :
    iSup (fun i => (s i).domain) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction_surjective X).surj y
  have hx : x ∈ iSup (fun i => (s i).baseOpen X L e₀) := by rw [hs]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem normalizedDualFrameClass_zero_trivial {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (hs : iSup (fun i => (s i).baseOpen X L e₀) = ⊤)
    (hz : DeformationClass.normalizedDualFrameClass X L e₀ s hs = 0) :
    Nonempty (L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule (LieRanks.dualNumberTest ℂ ⊗ X).left) := by
  obtain ⟨g, _, hg⟩ := DeformationClass.normalizedDualFrameClass_zero_gauge X L e₀ s hs hz
  obtain ⟨r, hr⟩ := Dual.CechCoefficient.exists_regular_gauge_of_dual_cech X (fun i => (s i).domain) (fun i => (s i).affine)
    (fun a => ((s (a 0)).localFrame X L e₀).transition ((s (a 1)).localFrame X L e₀)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1)) g hg
  exact Intrinsic.TransitionGaugeGluing.exists_trivialization_of_cech_frame_gauge (fun i => (s i).localFrame X L e₀)
    (normalizedDualFrames_cover_family X L e₀ s hs) r hr

theorem dualLineDeformationClass_zero_trivial (hz : DeformationClass.dualLineDeformationClass X L e₀ = 0) :
    Nonempty (L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule (LieRanks.dualNumberTest ℂ ⊗ X).left) :=
  normalizedDualFrameClass_zero_trivial X L e₀ (Dual.NormalizedFrameCover.normalizedDualFrameAt X L e₀)
    (Dual.NormalizedFrameCover.normalizedDualFrameCover_base X L e₀) hz

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.DeformationTriviality
