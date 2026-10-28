import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionCocycles

/-! # Frame Comparison Transitions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameComparisonTransitions

noncomputable section

/-! Matching scalar transition functions make the local comparisons
between two systems of frames agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {M N : X.Modules}

theorem frameComparison_eq_of_transition
    (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (g h : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (he : FrameTransitionCocycles.frameTransitionValue e f = FrameTransitionCocycles.frameTransitionValue g h) :
    e.hom ≫ g.inv = f.hom ≫ h.inv := by
  have hv : e.inv ≫ f.hom = g.inv ≫ h.hom := AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X he
  apply (cancel_epi e.inv).mp
  apply (cancel_mono h.hom).mp
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hv.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameComparisonTransitions
