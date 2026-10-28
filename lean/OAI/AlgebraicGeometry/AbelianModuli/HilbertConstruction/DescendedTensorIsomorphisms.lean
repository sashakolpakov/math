import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

/-! # Descended Tensor Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorIsomorphisms

noncomputable section

/-! Descended coefficient-compatible maps retain bijective recovery through repeated scalar extensions. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem descended_tensorMap_bijective (D : Subalgebra C R)
    (φ : R ⊗[C] A →ₐ[R] R ⊗[C] B) (ψ : D ⊗[C] A →ₐ[D] D ⊗[C] B)
    (h : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ (Coefficient.TensorMaps.coefficientTensorMap D x))
    (hφ : Function.Bijective φ) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R) ψ) := by
  let eA := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A) D
  let eB := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B) D
  have hw (x : R ⊗[D] (D ⊗[C] A)) :
      eB (Algebra.TensorProduct.map (AlgHom.id R R) ψ x) = φ (eA x) :=
    DFunLike.congr_fun (DescendedTensorMapComparison.descended_tensorMap_comparison D φ ψ h) x
  refine ⟨?_, DescendedTensorSurjectivity.descended_tensorMap_surjective D φ ψ h hφ.2⟩
  intro x y hxy
  apply eA.injective
  apply hφ.1
  exact (hw x).symm.trans ((congrArg eB hxy).trans (hw y))

theorem iterated_tensorMap_bijective (D : Subalgebra C R) (φ : A →ₐ[C] B)
    (hφ : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R) φ)) :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R)
      (Algebra.TensorProduct.map (AlgHom.id D D) φ)) :=
  descended_tensorMap_bijective D (Algebra.TensorProduct.map (AlgHom.id R R) φ)
    (Algebra.TensorProduct.map (AlgHom.id D D) φ) (NaturalTensorMapDescent.coefficientTensorMap_natural D φ) hφ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorIsomorphisms
