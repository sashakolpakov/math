import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalSchemeCocycle

/-! # Scheme Cocycle Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleTransport

noncomputable section

/-! Natural regular cocycles pull back along actual group-scheme homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {H K : Over S} [GrpObj H] [GrpObj K]
  (f : H ⟶ K) [IsMonHom f] (C : NaturalSchemeCocycle.NaturalCocycle K)

/-- Restrict every coefficient along the actual homomorphism on test points. -/
def pullback : NaturalSchemeCocycle.NaturalCocycle H where
  value a b := C.value (a ≫ f) (b ≫ f)
  natural g a b := by
    simpa only [Category.assoc] using C.natural g (a ≫ f) (b ≫ f)
  one_left a := by rw [MonObj.one_comp, C.one_left]
  one_right a := by rw [MonObj.one_comp, C.one_right]
  symmetric a b := C.symmetric (a ≫ f) (b ≫ f)
  cocycle a b c := by
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact C.cocycle (a ≫ f) (b ≫ f) (c ≫ f)

theorem value {T : Over S} (a b : T ⟶ H) :
    (pullback f C).value a b = C.value (a ≫ f) (b ≫ f) := rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeCocycleTransport
