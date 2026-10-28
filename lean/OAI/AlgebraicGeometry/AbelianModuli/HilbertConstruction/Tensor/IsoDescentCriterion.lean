import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MapRangeCriterion

/-! # Iso Descent Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.IsoDescentCriterion

noncomputable section

/-! An isomorphism descends over a fixed coefficient algebra when it and its inverse have coefficient-valued images. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B] [Module.Flat C A] [Module.Flat C B]

theorem existsUnique_flat_tensorIso_of_range (D : Subalgebra C R)
    (e : R ⊗[C] A ≃ₐ[R] R ⊗[C] B)
    (hA : ∀ a, e (1 ⊗ₜ[C] a) ∈ (Coefficient.TensorMaps.coefficientTensorMap D).range)
    (hB : ∀ b, e.symm (1 ⊗ₜ[C] b) ∈ (Coefficient.TensorMaps.coefficientTensorMap D).range) :
    ∃! eD : D ⊗[C] A ≃ₐ[D] D ⊗[C] B,
      (∀ x, Coefficient.TensorMaps.coefficientTensorMap D (eD x) = e (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
      (∀ y, Coefficient.TensorMaps.coefficientTensorMap D (eD.symm y) = e.symm (Coefficient.TensorMaps.coefficientTensorMap D y)) := by
  obtain ⟨f, hf, _⟩ := HilbertConstruction.Flat.MapRangeCriterion.existsUnique_flat_tensorHom_descent_of_range D e.toAlgHom hA
  obtain ⟨g, hg, _⟩ := HilbertConstruction.Flat.MapRangeCriterion.existsUnique_flat_tensorHom_descent_of_range D e.symm.toAlgHom hB
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
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, ⟨hf, hg⟩, ?_⟩
  intro d hd
  apply AlgEquiv.ext
  intro x
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  exact (hd.1 x).trans (hf x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.IsoDescentCriterion
