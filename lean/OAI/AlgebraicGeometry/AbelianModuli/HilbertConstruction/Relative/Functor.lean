import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BaseChangeNaturality
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.Functor

noncomputable section

/-! The actual relative Hilbert-family presheaf and its restriction to locally noetherian test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def relativeProjectiveHilbertFunctor (n : ℕ) (P : Polynomial ℚ) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := RelativeProjective.Families.RelativeProjectiveHilbertFamily T.unop n P
  map f := TypeCat.ofHom (fun F => F.pullback f.unop)
  map_id T := by
    ext F
    exact F.pullback_id
  map_comp f g := by
    ext F
    exact (F.pullback_comp f.unop g.unop).symm

def locallyNoetherianTestProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun T => IsLocallyNoetherian T.left

abbrev LocallyNoetherianTest (S : Scheme.{u}) := (locallyNoetherianTestProperty S).FullSubcategory

instance locallyNoetherianTest_left {S : Scheme.{u}} (T : LocallyNoetherianTest S) :
    IsLocallyNoetherian T.obj.left := T.property

def locallyNoetherianHilbertFunctor (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    (LocallyNoetherianTest S)ᵒᵖ ⥤ Type u :=
  ((locallyNoetherianTestProperty S).ι ⋙ Over.forget S).op ⋙ relativeProjectiveHilbertFunctor n P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.Functor
