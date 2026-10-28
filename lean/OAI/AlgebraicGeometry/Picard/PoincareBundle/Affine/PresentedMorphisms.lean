import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingSquares

/-! # Presented Morphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

noncomputable section

/-!
# Affine module morphisms and their actual presented sheaf morphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback

variable {R S : CommRingCat.{u}} {M N : ModuleCat.{u} R}
  {X Y : (Spec R).Modules} (eM : (tilde.functor R).obj M ≅ X)
  (eN : (tilde.functor R).obj N ≅ Y) (a : M ⟶ N)

/-- The actual sheaf morphism represented by an affine module map. -/
def presentedMap : X ⟶ Y :=
  PresentedMapNaturality.presentedMap (tilde.functor R) eM eN a

/-- Naturality of the affine pullback presentation, retaining the actual geometric map. -/
def IsNaturalitySquare (f : R ⟶ S) : Prop :=
  (tilde.functor S).map ((ModuleCat.extendScalars f.hom).map a) ≫ (Gluing.comparison N eN f).hom =
    (Gluing.comparison M eM f).hom ≫
      (Scheme.Modules.pullback (Spec.map f)).map (presentedMap eM eN a)

theorem comparison_naturality (f : R ⟶ S) : IsNaturalitySquare eM eN a f :=
  PresentedMapNaturality.naturality (ModuleCat.extendScalars f.hom) (tilde.functor R)
    (tilde.functor S) (Scheme.Modules.pullback (Spec.map f)) (TildePullback.tildePullbackIso f).symm eM eN a

variable (M)

/-- Transporting geometric gluing gives its actual commuting affine comparison square. -/
theorem moduleHom_square (i j : R ⟶ S)
    (σ : (Scheme.Modules.pullback (Spec.map i)).obj X ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj X) :
    (tilde.functor S).map (Gluing.moduleHom M eM i j σ) ≫ (Gluing.comparison M eM j).hom =
      (Gluing.comparison M eM i).hom ≫ σ :=
  GluingSquares.unconjugate (Gluing.comparison M eM i) (Gluing.comparison M eM j)
    ((tilde.functor S).map (Gluing.moduleHom M eM i j σ)) σ (Gluing.map_moduleHom M eM i j σ)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms
