import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorCoefficients
import Mathlib.RingTheory.Ideal.Operations

/-! # Principal Cover Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.PrincipalCoverDescent

noncomputable section

/-! A finite principal-open cover after coefficient extension already covers over finite coefficients. -/

open TensorProduct
open scoped BigOperators

universe u v

variable {C R A : Type u} [CommRing C] [CommRing R] [CommRing A]
variable [Algebra C R] [Algebra C A] [Module.Flat C A]

theorem exists_flat_principal_cover_descent {ι : Type v} [Finite ι] (f : ι → A)
    (hf : Ideal.span (Set.range (fun i => (1 : R) ⊗ₜ[C] f i)) = ⊤)
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      Ideal.span (Set.range (fun i => (1 : D) ⊗ₜ[C] f i)) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hf)
  obtain ⟨D, hED, hD, hcoeff⟩ := HilbertConstruction.Finite.TensorCoefficients.exists_finite_tensor_coefficients v E hE
  choose w hw using hcoeff
  refine ⟨D, hED, hD, (Ideal.eq_top_iff_one _).mpr ?_⟩
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨w, ?_⟩
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  calc
    Coefficient.TensorMaps.coefficientTensorMap D (∑ i, w i * ((1 : D) ⊗ₜ[C] f i)) =
        ∑ i, Coefficient.TensorMaps.coefficientTensorMap D (w i) * Coefficient.TensorMaps.coefficientTensorMap D ((1 : D) ⊗ₜ[C] f i) := by
      simp only [map_sum, map_mul]
    _ = ∑ i, v i * ((1 : R) ⊗ₜ[C] f i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg₂ (· * ·) (show Coefficient.TensorMaps.coefficientTensorMap D (w i) = v i from hw i)
        (show Coefficient.TensorMaps.coefficientTensorMap D ((1 : D) ⊗ₜ[C] f i) = (1 : R) ⊗ₜ[C] f i from rfl)
    _ = 1 := hv
    _ = Coefficient.TensorMaps.coefficientTensorMap D 1 := (map_one (Coefficient.TensorMaps.coefficientTensorMap D)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.PrincipalCoverDescent
