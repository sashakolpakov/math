import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo

/-! # Ordinary Form Derivation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormDerivation.OrdinaryFormSlots

noncomputable section

/-! # Each slot of the original differential symbol is a derivation -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (v : Fin n → A) (i : Fin n)

def derivation : Derivation R A (DeRhamPresentationTo.DeRhamPresentation.Form R A n) where
  __ := (DeRhamPresentationTo.DeRhamPresentation.symbols R A n).toMultilinearMap.toLinearMap v i
  map_one_eq_zero' := by
    change DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Function.update v i 1) = 0
    simpa only [map_one] using DeRhamPresentationTo.DeRhamPresentation.symbol_update_base R A v i 1
  leibniz' := DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul R A v i

theorem derivation_apply (a : A) :
    derivation R A v i a = DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Function.update v i a) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormDerivation.OrdinaryFormSlots
