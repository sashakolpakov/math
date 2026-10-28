import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorMapComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineImmersionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatTensorHomDescent

/-! # Concrete Affine Immersion Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineImmersionModels

noncomputable section

/-! Actual affine open-immersion maps, chosen over the original base, descend over common coefficients. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem exists_common_flat_openImmersion_models
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {ι : Type v} [Finite ι] (A B : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
    [∀ i, Algebra.FiniteType C (A i)] [∀ i, Algebra.FiniteType C (B i)]
    [∀ i, Module.Flat C (A i)] [∀ i, Module.Flat C (B i)]
    (φ : ∀ i, R ⊗[C] A i →ₐ[R] R ⊗[C] B i)
    [∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ i).toRingHom))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃ ψ : ∀ i, D ⊗[C] A i →ₐ[D] D ⊗[C] B i,
        (∀ i x, Coefficient.TensorMaps.coefficientTensorMap D (ψ i x) = φ i (Coefficient.TensorMaps.coefficientTensorMap D x)) ∧
        ∃ F : Subalgebra D R, F.FG ∧
          ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom
            (R := F ⊗[D] (D ⊗[C] A i)) (S := F ⊗[D] (D ⊗[C] B i))
            (Algebra.TensorProduct.map (AlgHom.id F F) (ψ i)).toRingHom)) := by
  obtain ⟨D, hED, hD, hd⟩ := HilbertConstruction.Finite.FlatTensorHomDescent.exists_common_flat_tensorHom_descent A B φ E hE
  choose ψ hψ _ using hd
  have (i : ι) : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (R := R ⊗[D] (D ⊗[C] A i)) (S := R ⊗[D] (D ⊗[C] B i))
      (Algebra.TensorProduct.map (AlgHom.id R R) (ψ i)).toRingHom)) :=
    DescendedTensorMapComparison.descended_tensorMap_isOpenImmersion D (φ i) (ψ i) (hψ i)
  obtain ⟨F, _, hF, hImm⟩ := HilbertConstruction.Finite.AffineImmersionDescent.exists_common_flat_affine_openImmersion_descent
    (C := D) (R := R) (fun i => D ⊗[C] A i) (fun i => D ⊗[C] B i)
    ψ (⊥ : Subalgebra D R) Subalgebra.fg_bot
  exact ⟨D, hED, hD, ψ, hψ, F, hF, hImm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConcreteAffineImmersionModels
