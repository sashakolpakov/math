import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

/-! # Morphism Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismEquality

noncomputable section

/-! Equality after geometric family base change is exactly equality after categorical pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem geometricFamilyMorphismBaseChange_eq_iff {S : Scheme.{u}} {U T A B : Over S}
    (c : U ⟶ T) (f q : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    MorphismBaseChange.geometricFamilyMorphismBaseChange c f = MorphismBaseChange.geometricFamilyMorphismBaseChange c q ↔
      (Over.pullback c.left).map f = (Over.pullback c.left).map q := by
  simp only [MorphismBaseChange.geometricFamilyMorphismBaseChange, cancel_epi, cancel_mono]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismEquality
