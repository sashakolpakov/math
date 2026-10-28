import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AlgebraMapDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MapRangeCriterion

/-! # Flat Tensor Hom Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorHomDescent

noncomputable section

/-! Finitely many maps between flat finite type models descend over one finite coefficient algebra. -/

open TensorProduct

universe u v

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {ι : Type v} [Finite ι] (A B : ι → Type u)
variable [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
variable [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
variable [∀ i, Algebra.FiniteType C (A i)] [∀ i, Module.Flat C (B i)]

theorem exists_common_flat_tensorHom_descent
    (φ : ∀ i, R ⊗[C] A i →ₐ[R] R ⊗[C] B i) (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, ∃! ψ : D ⊗[C] A i →ₐ[D] D ⊗[C] B i,
        ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ i (Coefficient.TensorMaps.coefficientTensorMap D x) := by
  choose D hED hD hφ using fun i => HilbertConstruction.Flat.AlgebraMapDescent.finiteType_algHom_coefficient_range
    ((AlgHom.liftEquiv C R (A i) (R ⊗[C] B i)).symm (φ i)) E hE
  obtain ⟨F, hF, hbound⟩ := CoefficientUpperBounds.exists_finiteType_coefficient_upperBound D hD
  refine ⟨E ⊔ F, le_sup_left, hE.sup hF, ?_⟩
  intro i
  apply HilbertConstruction.Flat.MapRangeCriterion.existsUnique_flat_tensorHom_descent_of_range
  intro a
  exact Coefficient.TensorMaps.coefficientTensorMap_range_mono ((hbound i).trans le_sup_right) (hφ i a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorHomDescent
