import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomExt

/-! # Algebraic Ring Hom Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomCoordinates.CommAlgebraicRingHomCoordinates

noncomputable section

/-! Unapplied ring coordinates of algebra-map composition. -/

open _root_.CategoryTheory

universe u v
variable {R : Type u} [CommRing R] {A B C : CommAlgCat.{v} R}

theorem comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.toRingHom = g.hom.toRingHom.comp f.hom.toRingHom := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomCoordinates.CommAlgebraicRingHomCoordinates
