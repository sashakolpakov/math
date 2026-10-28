import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFinite

/-! # Map Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapBaseChange.Construction

noncomputable section

/-! Actual geometric-fiber morphisms are base changes of their underlying scheme morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k]
  {A B : Over (Spec (CommRingCat.of k))} (f : A ⟶ B)

/-- The actual geometric-fiber map is the pullback of the given scheme map. -/
theorem geometricFiberMap_isPullback :
    IsPullback (Frobenius.Construction.geometricFiberMap k f) (pullback.fst A.hom (Frobenius.Construction.algebraicClosureBase k))
      (pullback.fst B.hom (Frobenius.Construction.algebraicClosureBase k)) f.left := by
  refine .of_right (t := (IsPullback.of_hasPullback B.hom (Frobenius.Construction.algebraicClosureBase k)).flip) ?_ ?_
  · rw [Frobenius.Construction.geometricFiberMap_snd, f.w]
    exact (IsPullback.of_hasPullback A.hom (Frobenius.Construction.algebraicClosureBase k)).flip
  · exact Frobenius.Construction.geometricFiberMap_fst k f

instance geometricFiberMap_finite [IsFinite f.left] : IsFinite (Frobenius.Construction.geometricFiberMap k f) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (geometricFiberMap_isPullback k f).flip inferInstance

instance geometricFiberMap_surjective [Surjective f.left] : Surjective (Frobenius.Construction.geometricFiberMap k f) :=
  MorphismProperty.of_isPullback (P := @Surjective) (geometricFiberMap_isPullback k f).flip inferInstance

variable (A) [Fintype k]

/-- Finiteness of the literal geometric Frobenius used in Completion. -/
theorem geometricSchemeFrobenius_finite [LocallyOfFiniteType A.hom] :
    IsFinite (Frobenius.Construction.geometricSchemeFrobenius k A) := by
  have := FrobeniusFinite.Construction.finiteFieldSchemeFrobenius_finite k A
  exact geometricFiberMap_finite k (Frobenius.Construction.finiteFieldSchemeFrobenius k A)

/-- Surjectivity of the literal geometric Frobenius used in Completion. -/
theorem geometricSchemeFrobenius_surjective : Surjective (Frobenius.Construction.geometricSchemeFrobenius k A) := by
  have := FrobeniusFinite.Construction.finiteFieldSchemeFrobenius_surjective k A
  exact geometricFiberMap_surjective k (Frobenius.Construction.finiteFieldSchemeFrobenius k A)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapBaseChange.Construction
