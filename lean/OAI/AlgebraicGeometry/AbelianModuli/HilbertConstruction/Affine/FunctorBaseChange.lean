import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor

/-! # Functor Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FunctorBaseChange

noncomputable section

/-! Base change preserves affine chart diagrams, finite-type structure maps, and open arrows. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

variable {C D : Type u} [CommRing C] [CommRing D]
variable {J : Type v} [Category.{w} J] (F : J ⥤ Over (Spec (.of C)))
variable (c : Spec (.of D) ⟶ Spec (.of C))

theorem affineFunctorBaseChange_affine [∀ i, IsAffine (F.obj i).left] (i : J) :
    IsAffine ((F ⋙ Over.pullback c).obj i).left := by
  change IsAffine (pullback (F.obj i).hom c)
  infer_instance

theorem affineFunctorBaseChange_finiteType [∀ i, LocallyOfFiniteType (F.obj i).hom] (i : J) :
    LocallyOfFiniteType ((F ⋙ Over.pullback c).obj i).hom := by
  change LocallyOfFiniteType (pullback.snd (F.obj i).hom c)
  infer_instance

theorem affineFunctorBaseChange_open
    [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f).left] {i j : J} (f : i ⟶ j) :
    IsOpenImmersion ((F ⋙ Over.pullback c).map f).left :=
  MorphismProperty.of_isPullback (Projective.PresentationBaseChange.overPullback_map_isPullback (F.map f) c) inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FunctorBaseChange
