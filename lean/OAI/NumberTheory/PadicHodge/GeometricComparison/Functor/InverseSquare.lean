import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtendedSection

/-! # Inverse Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.InverseSquare.FunctorInverseSquare

/-! Functorial transport of a commuting square through the
inverse of its two original coordinate isomorphisms. -/

open _root_.CategoryTheory

universe u v a b
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]
  (F : C ⥤ D) {A B A' B' : C} (e : A ≅ A') (d : B ≅ B')
  (f : A ⟶ B) (g : A' ⟶ B') (h : f ≫ d.hom = e.hom ≫ g)

include h in
theorem square : F.map g ≫ F.map d.inv = F.map e.inv ≫ F.map f :=
  (F.map_comp _ _).symm.trans
    ((congrArg F.map (ExtendedSection.ExtendedSectionHomology.inverse_square e d f g h)).trans (F.map_comp _ _))

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.InverseSquare.FunctorInverseSquare
