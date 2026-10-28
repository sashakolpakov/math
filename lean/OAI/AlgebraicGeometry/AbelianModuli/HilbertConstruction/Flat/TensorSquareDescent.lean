import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

/-! # Tensor Square Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorSquareDescent

noncomputable section

/-! Coefficient-compatible chart maps retain a commuting square when its receiving algebra is flat. -/

open TensorProduct

universe u

theorem flat_tensor_square_descent
    {C R A₁ A₂ B₁ B₂ : Type u}
    [CommRing C] [CommRing R] [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [Algebra C R] [Algebra C A₁] [Algebra C A₂] [Algebra C B₁] [Algebra C B₂]
    [Module.Flat C B₂] (D : Subalgebra C R)
    (a : A₁ →ₐ[C] A₂) (b : B₁ →ₐ[C] B₂)
    (f₁ : R ⊗[C] A₁ →ₐ[R] R ⊗[C] B₁) (f₂ : R ⊗[C] A₂ →ₐ[R] R ⊗[C] B₂)
    (g₁ : D ⊗[C] A₁ →ₐ[D] D ⊗[C] B₁) (g₂ : D ⊗[C] A₂ →ₐ[D] D ⊗[C] B₂)
    (h₁ : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (g₁ x) = f₁ (Coefficient.TensorMaps.coefficientTensorMap D x))
    (h₂ : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (g₂ x) = f₂ (Coefficient.TensorMaps.coefficientTensorMap D x))
    (hR : f₂.comp (Algebra.TensorProduct.map (AlgHom.id R R) a) =
      (Algebra.TensorProduct.map (AlgHom.id R R) b).comp f₁) :
    g₂.comp (Algebra.TensorProduct.map (AlgHom.id D D) a) =
      (Algebra.TensorProduct.map (AlgHom.id D D) b).comp g₁ := by
  apply AlgHom.ext
  intro x
  apply Coefficient.TensorMaps.coefficientTensorMap_injective D
  change Coefficient.TensorMaps.coefficientTensorMap D (g₂ (Algebra.TensorProduct.map (AlgHom.id D D) a x)) =
    Coefficient.TensorMaps.coefficientTensorMap D (Algebra.TensorProduct.map (AlgHom.id D D) b (g₁ x))
  calc
    _ = f₂ (Coefficient.TensorMaps.coefficientTensorMap D (Algebra.TensorProduct.map (AlgHom.id D D) a x)) := h₂ _
    _ = f₂ (Algebra.TensorProduct.map (AlgHom.id R R) a (Coefficient.TensorMaps.coefficientTensorMap D x)) :=
      congrArg f₂ (NaturalTensorMapDescent.coefficientTensorMap_natural D a x)
    _ = Algebra.TensorProduct.map (AlgHom.id R R) b (f₁ (Coefficient.TensorMaps.coefficientTensorMap D x)) :=
      DFunLike.congr_fun hR (Coefficient.TensorMaps.coefficientTensorMap D x)
    _ = Algebra.TensorProduct.map (AlgHom.id R R) b (Coefficient.TensorMaps.coefficientTensorMap D (g₁ x)) :=
      congrArg (Algebra.TensorProduct.map (AlgHom.id R R) b) (h₁ x).symm
    _ = _ := (NaturalTensorMapDescent.coefficientTensorMap_natural D b (g₁ x)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.TensorSquareDescent
