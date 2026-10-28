import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.MapSurjectiveGenerators

/-! # Natural Tensor Surjection Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorSurjectionDescent

noncomputable section

/-! Surjectivity of a natural tensor map descends when its target algebra is flat and finitely generated. -/

open TensorProduct

universe u

theorem exists_natural_tensorMap_surjective
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B] [Module.Flat C B] [Algebra.FiniteType C B]
    (φ : A →ₐ[C] B) (hφ : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R R) φ))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id D D) φ) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := C) (A := B)
  choose x hx using fun b : s => hφ ((1 : R) ⊗ₜ[C] b.val)
  obtain ⟨D, hED, hD, hd⟩ := Finite.TensorCoefficients.exists_finite_tensor_coefficients x E hE
  refine ⟨D, hED, hD, Tensor.MapSurjectiveGenerators.tensorMap_surjective_of_generators φ (s : Set B) hs ?_⟩
  intro b hb
  obtain ⟨y, hy⟩ := hd ⟨b, hb⟩
  change Coefficient.TensorMaps.coefficientTensorMap D y = x ⟨b, hb⟩ at hy
  refine ⟨y, ?_⟩
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  rw [NaturalTensorMapDescent.coefficientTensorMap_natural, hy]
  exact hx ⟨b, hb⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorSurjectionDescent
