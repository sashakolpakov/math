import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorSurjectionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorHomDescent
import Mathlib.RingTheory.FiniteStability

/-! # Concrete Affine Surjection Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineSurjectionModels

noncomputable section

/-! Actual surjective affine coordinate maps descend over common coefficients with flat targets. -/

open TensorProduct

universe u v

theorem exists_common_flat_surjective_models
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
          ∀ i, Function.Surjective (Algebra.TensorProduct.map (AlgHom.id F F) (ψ i)) := by
  obtain ⟨D, hED, hD, hd⟩ := HilbertConstruction.Finite.FlatTensorHomDescent.exists_common_flat_tensorHom_descent A B φ E hE
  choose ψ hψ _ using hd
  have hR (i : I) : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R R) (ψ i)) :=
    DescendedTensorSurjectivity.descended_tensorMap_surjective D (φ i) (ψ i) (hψ i) (hφ i)
  obtain ⟨F, _, hF, hf⟩ := HilbertConstruction.Finite.TensorSurjectionDescent.exists_common_natural_tensorMap_surjective
    (C := D) (R := R) (fun i => D ⊗[C] A i) (fun i => D ⊗[C] B i)
    ψ hR (⊥ : Subalgebra D R) Subalgebra.fg_bot
  exact ⟨D, hED, hD, ψ, hψ, F, hF, hf⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineSurjectionModels
