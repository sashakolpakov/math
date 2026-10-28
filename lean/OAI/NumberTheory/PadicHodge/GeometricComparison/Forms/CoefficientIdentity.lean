import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Coefficient Identity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientIdentity.FormsCoefficientIdentity

noncomputable section

/-! Equal coefficient-algebra structures identify the actual relative-form modules canonically. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R B : Type u) [CommRing R] [CommRing B]

def module (α : Algebra R B) (n : ℕ) : ModuleCat.{u} R := by
  letI := α
  exact ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n)

def iso (α β : Algebra R B) (h : α = β) (n : ℕ) : module R B α n ≅ module R B β n := by
  cases h
  exact Iso.refl _

theorem iso_symbol (α β : Algebra R B) (h : α = β) (n : ℕ) (b : B) (v : Fin n → B) :
    (iso R B α β h n).hom (@AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ α n b v) = @AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _ β n b v := by
  cases h
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoefficientIdentity.FormsCoefficientIdentity
