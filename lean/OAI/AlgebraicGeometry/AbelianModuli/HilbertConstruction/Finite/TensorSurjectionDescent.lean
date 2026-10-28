import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorSurjectionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DependentTensorCoefficients
import Mathlib.Basic.Finite.Sigma

/-! # Tensor Surjection Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorSurjectionDescent

noncomputable section

/-! Surjective tensor maps with flat finitely generated targets descend simultaneously over finite coefficients. -/

open TensorProduct

universe u v

theorem exists_common_natural_tensorMap_surjective
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {I : Type v} [Finite I] (A B : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
    [∀ i, Module.Flat C (B i)] [∀ i, Algebra.FiniteType C (B i)]
    (φ : ∀ i, A i →ₐ[C] B i)
    (hφ : ∀ i, Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R R) (φ i)))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, Function.Surjective (Algebra.TensorProduct.map (AlgHom.id D D) (φ i)) := by
  classical
  choose s hs using fun i => Algebra.FiniteType.out (R := C) (A := B i)
  let K := Σ i, ↥(s i)
  have : Finite K := inferInstanceAs (Finite (Σ i, ↥(s i)))
  choose x hx using fun k : K => hφ k.1 ((1 : R) ⊗ₜ[C] k.2.val)
  obtain ⟨D, hED, hD, hd⟩ := DependentTensorCoefficients.exists_dependent_tensor_coefficients (fun k : K => A k.1) x E hE
  refine ⟨D, hED, hD, ?_⟩
  intro i
  apply Tensor.MapSurjectiveGenerators.tensorMap_surjective_of_generators (φ i) (s i : Set (B i)) (hs i)
  intro b hb
  obtain ⟨y, hy⟩ := hd ⟨i, b, hb⟩
  change Coefficient.TensorMaps.coefficientTensorMap D y = x ⟨i, b, hb⟩ at hy
  refine ⟨y, ?_⟩
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  rw [NaturalTensorMapDescent.coefficientTensorMap_natural, hy]
  exact hx ⟨i, b, hb⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorSurjectionDescent
