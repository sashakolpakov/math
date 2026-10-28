import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientUpperBounds

/-! # Tensor Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorCoefficients

noncomputable section

/-! Finitely many tensor elements lift over one finite coefficient subalgebra. -/

open TensorProduct

universe u v

variable {C R B : Type u} [CommRing C] [CommRing R] [CommRing B] [Algebra C R] [Algebra C B]

theorem exists_tensor_coefficient_range (x : R ⊗[C] B) :
    ∃ D : Subalgebra C R, D.FG ∧ x ∈ (Coefficient.TensorMaps.coefficientTensorMap (B := B) D).range := by
  obtain ⟨D, hD, y, hy⟩ := TensorProduct.Algebra.exists_of_fg x
  exact ⟨D, hD, y,
    (DFunLike.congr_fun (Coefficient.TensorMaps.coefficientTensorMap_toLinearMap (B := B) D) y).trans hy⟩

theorem exists_finite_tensor_coefficients {ι : Type v} [Finite ι] (x : ι → R ⊗[C] B)
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧ ∀ i, x i ∈ (Coefficient.TensorMaps.coefficientTensorMap (B := B) D).range := by
  choose D hD hx using fun i => exists_tensor_coefficient_range (x i)
  obtain ⟨F, hF, hbound⟩ := CoefficientUpperBounds.exists_finiteType_coefficient_upperBound D hD
  refine ⟨E ⊔ F, le_sup_left, hE.sup hF, ?_⟩
  intro i
  exact Coefficient.TensorMaps.coefficientTensorMap_range_mono ((hbound i).trans le_sup_right) (hx i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorCoefficients
