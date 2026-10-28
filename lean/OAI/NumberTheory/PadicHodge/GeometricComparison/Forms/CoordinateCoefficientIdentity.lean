import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Coordinate Coefficient Identity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateCoefficientIdentity.FormsCoordinateCoefficientIdentity

noncomputable section

/-! Equal base and coordinate actions identify the same native form symbols as coordinate modules. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

def module (α : Algebra R B) (γ : Algebra A B) (n : ℕ) : ModuleCat.{u} A := by
  let := α
  let := γ
  exact ModuleCat.of A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)

def iso (α β : Algebra R B) (γ δ : Algebra A B) (h : α = β) (k : γ = δ) (n : ℕ) :
    module R A B α γ n ≅ module R A B β δ n := by
  cases h
  cases k
  exact Iso.refl _

theorem iso_symbol (α β : Algebra R B) (γ δ : Algebra A B) (h : α = β) (k : γ = δ)
    (n : ℕ) (b : B) (v : Fin n → B) :
    (iso R A B α β γ δ h k n).hom (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ α n b v) = @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ β n b v := by
  cases h
  cases k
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateCoefficientIdentity.FormsCoordinateCoefficientIdentity
