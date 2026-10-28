import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.AffineModelRecovery

/-! # Smooth Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.SmoothModel

noncomputable section

/-! Smoothness survives both coefficient extensions in the explicit iterated model. -/

open TensorProduct

universe u

theorem iteratedCoefficientAlgebra_smooth
    {C R A₀ : Type u} [CommRing C] [CommRing R] [CommRing A₀]
    [Algebra C R] [Algebra C A₀] [Algebra.Smooth C A₀]
    (D : Subalgebra C R) (F : Subalgebra D R) :
    Algebra.Smooth F (AffineModelRecovery.iteratedCoefficientAlgebra (A₀ := A₀) D F) := by
  change Algebra.Smooth F (F ⊗[D] (D ⊗[C] A₀))
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.SmoothModel
