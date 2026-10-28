import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackIsoComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

/-! # Base Map Morphism Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapMorphismEquality

noncomputable section

/-! Conjugation by the parameter pullback comparison is injective and agrees with geometric base change on pulled-back maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem overBaseMapPullbackMorphism_injective
    {S : Scheme.{u}} {T M A B : Over S} (c : T ⟶ M) :
    Function.Injective (@BaseMapPullback.overBaseMapPullbackMorphism S T M A B c) := by
  intro f g h
  simpa only [BaseMapPullback.overBaseMapPullbackMorphism, cancel_epi, cancel_mono] using h

theorem overBaseMapPullbackMorphism_pullback
    {S : Scheme.{u}} {T M A B : Over S} (c : T ⟶ M)
    (f : (Over.pullback M.hom).obj A ⟶ (Over.pullback M.hom).obj B) :
    BaseMapPullback.overBaseMapPullbackMorphism c ((Over.pullback c.left).map f) = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c f := by
  unfold BaseMapPullback.overBaseMapPullbackMorphism Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange
  rw [ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter, ParameterPullbackIsoComparison.overBaseMapPullbackIso_eq_singleParameter]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.BaseMapMorphismEquality
