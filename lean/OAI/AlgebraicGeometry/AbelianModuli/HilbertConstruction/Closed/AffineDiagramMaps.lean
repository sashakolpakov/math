import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineClosedModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorSquareDescent

/-! # Affine Diagram Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AffineDiagramMaps

noncomputable section

/-! Closed affine chart maps descend together while retaining compatibility with every diagram arrow. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_common_closed_affine_diagram_maps
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {I : Type v} [Finite I] (A B : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
    [∀ i, Algebra.FiniteType C (A i)] [∀ i, Algebra.FiniteType C (B i)]
    [∀ i, Module.Flat C (B i)]
    {J : Type w} (s t : J → I) (a : ∀ j, A (s j) →ₐ[C] A (t j)) (b : ∀ j, B (s j) →ₐ[C] B (t j))
    (φ : ∀ i, R ⊗[C] A i →ₐ[R] R ⊗[C] B i) (hφ : ∀ i, Function.Surjective (φ i))
    (hnat : ∀ j, (φ (t j)).comp (Algebra.TensorProduct.map (AlgHom.id R R) (a j)) =
      (Algebra.TensorProduct.map (AlgHom.id R R) (b j)).comp (φ (s j)))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃ ψ : ∀ i, D ⊗[C] A i →ₐ[D] D ⊗[C] B i,
        (∀ i x, Coefficient.TensorMaps.coefficientTensorMap D (ψ i x) = φ i (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
        (∀ j, (ψ (t j)).comp (Algebra.TensorProduct.map (AlgHom.id D D) (a j)) =
          (Algebra.TensorProduct.map (AlgHom.id D D) (b j)).comp (ψ (s j))) ∧
        ∃ F : Subalgebra D R, F.FG ∧
          ∀ i, IsClosedImmersion (Spec.map (CommRingCat.ofHom
            (R := F ⊗[D] (D ⊗[C] A i)) (S := F ⊗[D] (D ⊗[C] B i))
            (Algebra.TensorProduct.map (AlgHom.id F F) (ψ i)).toRingHom)) := by
  obtain ⟨D, hED, hD, ψ, hψ, F, hF, hf⟩ := ConcreteAffineClosedModels.exists_common_flat_closedImmersion_models A B φ hφ E hE
  refine ⟨D, hED, hD, ψ, hψ, ?_, F, hF, hf⟩
  intro j
  exact HilbertConstruction.Flat.TensorSquareDescent.flat_tensor_square_descent D (a j) (b j) (φ (s j)) (φ (t j))
    (ψ (s j)) (ψ (t j)) (hψ (s j)) (hψ (t j)) (hnat j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.AffineDiagramMaps
