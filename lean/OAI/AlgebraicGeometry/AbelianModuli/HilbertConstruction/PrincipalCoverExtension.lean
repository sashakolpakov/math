import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.PrincipalCoverDescent

/-! # Principal Cover Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalCoverExtension

noncomputable section

/-! A descended principal cover remains a cover after further coefficient extension. -/

open TensorProduct

universe u v

theorem principal_cover_coefficient_mono
    {C R A : Type u} [CommRing C] [CommRing R] [CommRing A]
    [Algebra C R] [Algebra C A] {D E : Subalgebra C R} (h : D ≤ E)
    {ι : Type v} (f : ι → A)
    (hf : Ideal.span (Set.range (fun i => (1 : D) ⊗ₜ[C] f i)) = ⊤) :
    Ideal.span (Set.range (fun i => (1 : E) ⊗ₜ[C] f i)) = ⊤ := by
  have heq := congrArg (Ideal.map (Coefficient.TensorMaps.coefficientTensorInclusion (B := A) h).toRingHom) hf
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at heq
  exact heq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalCoverExtension
