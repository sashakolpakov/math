import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandTransport
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Filtered Hecke Dimension Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredHeckeDimensionTransport.GeneralizedHecke

noncomputable section

/-! Actual intertwining filtered equivalences identify the dimensions of all filtered generalized Hecke summands. -/

variable {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem filtered_summand_map (e : V ≃ₗ[K] W) (T : I → Module.End K V) (U : I → Module.End K W)
    (h : ∀ i x, e (T i x) = U i (e x)) (χ : I → K)
    (P : Submodule K V) (Q : Submodule K W) (hP : P.map e.toLinearMap = Q) :
    (Linear.generalizedHeckeSummand T χ ⊓ P).map e.toLinearMap = Linear.generalizedHeckeSummand U χ ⊓ Q := by
  rw [Submodule.map_inf _ e.injective, HeckeSummandTransport.GeneralizedHecke.summand_map e T U h χ, hP]

theorem filtered_summand_finrank (e : V ≃ₗ[K] W) (T : I → Module.End K V) (U : I → Module.End K W)
    (h : ∀ i x, e (T i x) = U i (e x)) (χ : I → K)
    (P : Submodule K V) (Q : Submodule K W) (hP : P.map e.toLinearMap = Q) :
    Module.finrank K (Linear.generalizedHeckeSummand U χ ⊓ Q : Submodule K W) =
      Module.finrank K (Linear.generalizedHeckeSummand T χ ⊓ P : Submodule K V) := by
  rw [← filtered_summand_map e T U h χ P Q hP]
  exact e.finrank_map_eq _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredHeckeDimensionTransport.GeneralizedHecke
