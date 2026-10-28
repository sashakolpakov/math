import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

/-! # Morphism Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismIsomorphisms

noncomputable section

/-! Geometric family base change is an isomorphism exactly when the categorical pullback morphism is. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem geometricFamilyMorphismBaseChange_isIso_iff {S : Scheme.{u}} {U T A B : Over S}
    (c : U ⟶ T) (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    IsIso (MorphismBaseChange.geometricFamilyMorphismBaseChange c f) ↔ IsIso ((Over.pullback c.left).map f) := by
  simp only [MorphismBaseChange.geometricFamilyMorphismBaseChange, isIso_comp_left_iff, isIso_comp_right_iff]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismIsomorphisms
