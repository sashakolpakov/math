import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineSurjectionModels
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Concrete Affine Closed Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineClosedModels

noncomputable section

/-! Surjective coordinate-map descent produces actual closed affine chart embeddings over finite coefficients. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem exists_common_flat_closedImmersion_models
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {I : Type v} [Finite I] (A B : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
    [∀ i, Algebra.FiniteType C (A i)] [∀ i, Algebra.FiniteType C (B i)]
    [∀ i, Module.Flat C (B i)]
    (φ : ∀ i, R ⊗[C] A i →ₐ[R] R ⊗[C] B i) (hφ : ∀ i, Function.Surjective (φ i))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃ ψ : ∀ i, D ⊗[C] A i →ₐ[D] D ⊗[C] B i,
        (∀ i x, Coefficient.TensorMaps.coefficientTensorMap D (ψ i x) = φ i (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
        ∃ F : Subalgebra D R, F.FG ∧
          ∀ i, IsClosedImmersion (Spec.map (CommRingCat.ofHom
            (R := F ⊗[D] (D ⊗[C] A i)) (S := F ⊗[D] (D ⊗[C] B i))
            (Algebra.TensorProduct.map (AlgHom.id F F) (ψ i)).toRingHom)) := by
  obtain ⟨D, hED, hD, ψ, hψ, F, hF, hf⟩ := ConcreteAffineSurjectionModels.exists_common_flat_surjective_models A B φ hφ E hE
  exact ⟨D, hED, hD, ψ, hψ, F, hF, fun i => IsClosedImmersion.spec_of_surjective _ (hf i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineClosedModels
