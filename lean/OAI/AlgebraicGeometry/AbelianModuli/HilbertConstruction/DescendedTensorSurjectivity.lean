import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorMapComparison

/-! # Descended Tensor Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorSurjectivity

noncomputable section

/-! Coefficient-compatible maps recover surjectivity after iterated base change. -/

open TensorProduct

universe u

theorem descended_tensorMap_surjective
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B]
    (D : Subalgebra C R) (φ : R ⊗[C] A →ₐ[R] R ⊗[C] B)
    (ψ : D ⊗[C] A →ₐ[D] D ⊗[C] B)
    (h : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ (Coefficient.TensorMaps.coefficientTensorMap D x))
    (hφ : Function.Surjective φ) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R R) ψ) := by
  let eA := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A) D
  let eB := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B) D
  have hw (x : R ⊗[D] (D ⊗[C] A)) :
      eB (Algebra.TensorProduct.map (AlgHom.id R R) ψ x) = φ (eA x) :=
    DFunLike.congr_fun (DescendedTensorMapComparison.descended_tensorMap_comparison D φ ψ h) x
  intro y
  obtain ⟨x, hx⟩ := hφ (eB y)
  refine ⟨eA.symm x, eB.injective ?_⟩
  rw [hw, eA.apply_symm_apply, hx]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorSurjectivity
