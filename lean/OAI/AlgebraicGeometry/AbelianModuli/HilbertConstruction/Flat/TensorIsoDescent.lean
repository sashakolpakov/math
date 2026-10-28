import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AlgebraMapDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MapRangeCriterion

/-! # Tensor Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorIsoDescent

noncomputable section

/-! Isomorphisms between flat finite type models descend together with their inverses. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]
variable [Algebra.FiniteType C A] [Algebra.FiniteType C B] [Module.Flat C A] [Module.Flat C B]

theorem exists_flat_tensorIso_descent (e : R ⊗[C] A ≃ₐ[R] R ⊗[C] B)
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃ eD : D ⊗[C] A ≃ₐ[D] D ⊗[C] B,
        (∀ x, Coefficient.TensorMaps.coefficientTensorMap D (eD x) = e (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
        (∀ y, Coefficient.TensorMaps.coefficientTensorMap D (eD.symm y) = e.symm (Coefficient.TensorMaps.coefficientTensorMap D y)) := by
  obtain ⟨D₁, hE₁, hD₁, h₁⟩ := AlgebraMapDescent.finiteType_algHom_coefficient_range
    ((AlgHom.liftEquiv C R A (R ⊗[C] B)).symm e.toAlgHom) E hE
  obtain ⟨D₂, _, hD₂, h₂⟩ := AlgebraMapDescent.finiteType_algHom_coefficient_range
    ((AlgHom.liftEquiv C R B (R ⊗[C] A)).symm e.symm.toAlgHom) E hE
  let D := D₁ ⊔ D₂
  obtain ⟨f, hf, _⟩ := MapRangeCriterion.existsUnique_flat_tensorHom_descent_of_range D e.toAlgHom
    (fun a => Coefficient.TensorMaps.coefficientTensorMap_range_mono le_sup_left (h₁ a))
  obtain ⟨g, hg, _⟩ := MapRangeCriterion.existsUnique_flat_tensorHom_descent_of_range D e.symm.toAlgHom
    (fun b => Coefficient.TensorMaps.coefficientTensorMap_range_mono le_sup_right (h₂ b))
  have hfg : f.comp g = AlgHom.id D (D ⊗[C] B) := by
    apply AlgHom.ext
    intro y
    apply Coefficient.TensorMaps.coefficientTensorMap_injective D
    exact (hf (g y)).trans ((congrArg e (hg y)).trans (e.apply_symm_apply _))
  have hgf : g.comp f = AlgHom.id D (D ⊗[C] A) := by
    apply AlgHom.ext
    intro x
    apply Coefficient.TensorMaps.coefficientTensorMap_injective D
    exact (hg (f x)).trans ((congrArg e.symm (hf x)).trans (e.symm_apply_apply _))
  exact ⟨D, hE₁.trans le_sup_left, hD₁.sup hD₂, AlgEquiv.ofAlgHom f g hfg hgf, hf, hg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorIsoDescent
