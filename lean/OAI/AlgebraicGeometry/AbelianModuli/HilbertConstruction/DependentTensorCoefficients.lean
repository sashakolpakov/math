import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorCoefficients

/-! # Dependent Tensor Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DependentTensorCoefficients

noncomputable section

/-! Finitely many elements of different tensor-model algebras lift over one coefficient subalgebra. -/

open TensorProduct

universe u v

theorem exists_dependent_tensor_coefficients
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {ι : Type v} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra C (B i)]
    (x : ∀ i, R ⊗[C] B i) (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, x i ∈ (Coefficient.TensorMaps.coefficientTensorMap (B := B i) D).range := by
  choose F hF hx using fun i => HilbertConstruction.Finite.TensorCoefficients.exists_tensor_coefficient_range (x i)
  obtain ⟨G, hG, hbound⟩ := HilbertConstruction.Finite.CoefficientUpperBounds.exists_finiteType_coefficient_upperBound F hF
  refine ⟨E ⊔ G, le_sup_left, hE.sup hG, ?_⟩
  intro i
  exact Coefficient.TensorMaps.coefficientTensorMap_range_mono ((hbound i).trans le_sup_right) (hx i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DependentTensorCoefficients
