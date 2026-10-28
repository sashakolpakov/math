import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Descent Component Isomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms

noncomputable section

/-!
# Actual isomorphisms and evaluation for ordinary descent data on one cover
-/

open _root_.CategoryTheory Opposite

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {X Y : C} (f : X ⟶ Y)

/-- Evaluation keeps the actual source object and actual source morphism of a one-cover descent datum. -/
def evaluation : F.DescentData (fun (_ : PUnit.{1}) => f) ⥤ F.obj (.mk (op X)) where
  obj D := D.obj PUnit.unit
  map a := a.hom PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A genuine isomorphism of descent data has an actual isomorphism on its source objects. -/
def componentIso {D E : F.DescentData (fun (_ : PUnit.{1}) => f)} (e : D ≅ E) :
    D.obj PUnit.unit ≅ E.obj PUnit.unit := (evaluation F f).mapIso e

/-- An invertible actual source component makes a compatible morphism an isomorphism of the full descent data. -/
def isoOfComponent {D E : F.DescentData (fun (_ : PUnit.{1}) => f)}
    (a : D ⟶ E) [IsIso (a.hom PUnit.unit)] : D ≅ E :=
  Pseudofunctor.DescentData.isoMk (fun _ => asIso (a.hom PUnit.unit)) (by
    intro T q i j x y hx hy
    cases i
    cases j
    exact a.comm q x y hx hy)

/-- The constructed full isomorphism has precisely the original actual source component. -/
theorem isoOfComponent_hom {D E : F.DescentData (fun (_ : PUnit.{1}) => f)}
    (a : D ⟶ E) [IsIso (a.hom PUnit.unit)] : (isoOfComponent F f a).hom.hom PUnit.unit = a.hom PUnit.unit := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms
