import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor

/-! # Tensor Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap.KoszulTensorMap

noncomputable section

/-! # Maps of tensor coordinate complexes -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R σ M N : Type u) [CommRing R] [Fintype σ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (D : σ → Module.End R M) (E : σ → Module.End R N)
  (f : M →ₗ[R] N) (hf : ∀ i m, f (D i m) = E i (f m))

include hf in
theorem differential_naturality (n : ℕ) :
    (TensorProduct.map f (LinearMap.id : Module.End R (⋀[R]^(n + 1) (σ →₀ R)))).comp
      (Tensor.KoszulTensor.differential R σ M D n) =
        (Tensor.KoszulTensor.differential R σ N E n).comp
          (TensorProduct.map f (LinearMap.id : Module.End R (⋀[R]^n (σ →₀ R)))) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  change TensorProduct.map f LinearMap.id (Tensor.KoszulTensor.differential R σ M D n (m ⊗ₜ[R] ω)) =
    Tensor.KoszulTensor.differential R σ N E n (f m ⊗ₜ[R] ω)
  rw [Tensor.KoszulTensor.differential_tmul, map_sum, Tensor.KoszulTensor.differential_tmul]
  apply Finset.sum_congr rfl
  intro i _
  change f (D i m) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ i n ω =
    E i (f m) ⊗ₜ[R] Tensor.KoszulTensor.exteriorWedge R σ i n ω
  rw [hf]

variable (hD : ∀ i j, Function.Commute (D i) (D j))
  (hE : ∀ i j, Function.Commute (E i) (E j))

def map : Tensor.KoszulTensor.complex R σ M D hD ⟶ Tensor.KoszulTensor.complex R σ N E hE where
  f n := ModuleCat.ofHom (TensorProduct.map f (LinearMap.id : Module.End R (⋀[R]^n (σ →₀ R))))
  comm' n m hnm := by
    have hm : n + 1 = m := hnm
    subst m
    dsimp only [Tensor.KoszulTensor.complex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact (differential_naturality R σ M N D E f hf n).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap.KoszulTensorMap
