import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.IsoDescentCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AlgebraMapDescent

/-! # Flat Tensor Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorIsoDescent

noncomputable section

/-! A finite collection of isomorphisms and inverses descends over a common coefficient algebra. -/

open TensorProduct

universe u v

variable {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
variable {ι : Type v} [Finite ι] (A B : ι → Type u)
variable [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
variable [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
variable [∀ i, Algebra.FiniteType C (A i)] [∀ i, Algebra.FiniteType C (B i)]
variable [∀ i, Module.Flat C (A i)] [∀ i, Module.Flat C (B i)]

theorem exists_common_flat_tensorIso_descent
    (e : ∀ i, R ⊗[C] A i ≃ₐ[R] R ⊗[C] B i) (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, ∃! eD : D ⊗[C] A i ≃ₐ[D] D ⊗[C] B i,
        (∀ x, Coefficient.TensorMaps.coefficientTensorMap D (eD x) = e i (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
        (∀ y, Coefficient.TensorMaps.coefficientTensorMap D (eD.symm y) = (e i).symm (Coefficient.TensorMaps.coefficientTensorMap D y)) := by
  choose D₁ _ hD₁ h₁ using fun i => HilbertConstruction.Flat.AlgebraMapDescent.finiteType_algHom_coefficient_range
    ((AlgHom.liftEquiv C R (A i) (R ⊗[C] B i)).symm (e i).toAlgHom) E hE
  choose D₂ _ hD₂ h₂ using fun i => HilbertConstruction.Flat.AlgebraMapDescent.finiteType_algHom_coefficient_range
    ((AlgHom.liftEquiv C R (B i) (R ⊗[C] A i)).symm (e i).symm.toAlgHom) E hE
  obtain ⟨F₁, hF₁, hb₁⟩ := CoefficientUpperBounds.exists_finiteType_coefficient_upperBound D₁ hD₁
  obtain ⟨F₂, hF₂, hb₂⟩ := CoefficientUpperBounds.exists_finiteType_coefficient_upperBound D₂ hD₂
  let D := E ⊔ (F₁ ⊔ F₂)
  refine ⟨D, le_sup_left, hE.sup (hF₁.sup hF₂), ?_⟩
  intro i
  apply Tensor.IsoDescentCriterion.existsUnique_flat_tensorIso_of_range
  · intro a
    exact Coefficient.TensorMaps.coefficientTensorMap_range_mono ((hb₁ i).trans (le_sup_of_le_right le_sup_left)) (h₁ i a)
  · intro b
    exact Coefficient.TensorMaps.coefficientTensorMap_range_mono ((hb₂ i).trans (le_sup_of_le_right le_sup_right)) (h₂ i b)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorIsoDescent
