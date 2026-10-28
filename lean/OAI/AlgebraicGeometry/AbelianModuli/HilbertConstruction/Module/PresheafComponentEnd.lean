import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafScalarAction

/-! # Presheaf Component End -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.PresheafComponentEnd

noncomputable section

/-! Evaluation of a module-presheaf endomorphism on an open set is a ring homomorphism to coefficient-linear endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def modulePresheafComponentEndRingHom {X : Scheme.{u}} {R : Type u} [CommRing R]
    (F : TopCat.Presheaf (ModuleCat.{u} R) X) (U : X.Opens) :
    End F →+* Module.End R (F.obj (.op U)) where
  toFun e := (e.app (.op U)).hom
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.PresheafComponentEnd
