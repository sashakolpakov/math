import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismEquality

/-! # Morphism Field Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFieldEquality

noncomputable section

/-! Equality on all field pullbacks persists under the actual geometric base-change operation on family morphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem geometricFamilyMorphismBaseChange_fieldEquality
    {S : Scheme.{u}} {A B U T : Over S} (c : U ⟶ T)
    (f q : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) :
    ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ U.left),
      (Over.pullback s).map (MorphismBaseChange.geometricFamilyMorphismBaseChange c f) =
        (Over.pullback s).map (MorphismBaseChange.geometricFamilyMorphismBaseChange c q) := by
  intro K _ s
  let V : Over S := Over.mk (s ≫ U.hom)
  let d : V ⟶ U := Over.homMk s rfl
  apply (MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff d _ _).mp
  rw [MorphismFunctor.geometricFamilyMorphismBaseChange_composition, MorphismFunctor.geometricFamilyMorphismBaseChange_composition]
  exact (MorphismEquality.geometricFamilyMorphismBaseChange_eq_iff (d ≫ c) f q).mpr (h K (s ≫ c.left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFieldEquality
