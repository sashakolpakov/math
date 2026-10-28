import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor

/-! # Tensor Equivalence -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorEquivalence.KoszulTensorEquivalence

noncomputable section

/-! # Transport of tensor coordinate complexes along coefficient equivalences -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R σ M N : Type u) [CommRing R] [Fintype σ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (D : σ → Module.End R M) (E : σ → Module.End R N)
  (hD : ∀ i j, Function.Commute (D i) (D j))
  (hE : ∀ i j, Function.Commute (E i) (E j))
  (e : M ≃ₗ[R] N) (he : ∀ i m, e (D i m) = E i (e m))

def termEquiv (n : ℕ) : Tensor.KoszulTensor.Term R σ M n ≃ₗ[R] Tensor.KoszulTensor.Term R σ N n :=
  TensorProduct.congr e (LinearEquiv.refl R _)

include he in
theorem differential_compatibility (n : ℕ) :
    (termEquiv R σ M N e (n + 1)).toLinearMap.comp (Tensor.KoszulTensor.differential R σ M D n) =
      (Tensor.KoszulTensor.differential R σ N E n).comp (termEquiv R σ M N e n).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro ω
  change termEquiv R σ M N e (n + 1) (Tensor.KoszulTensor.differential R σ M D n (m ⊗ₜ[R] ω)) =
    Tensor.KoszulTensor.differential R σ N E n (e m ⊗ₜ[R] ω)
  rw [Tensor.KoszulTensor.differential_tmul, map_sum, Tensor.KoszulTensor.differential_tmul]
  apply Finset.sum_congr rfl
  intro i _
  change e (D i m) ⊗ₜ[R] _ = E i (e m) ⊗ₜ[R] _
  rw [he]
  rfl

def complexIso : Tensor.KoszulTensor.complex R σ M D hD ≅ Tensor.KoszulTensor.complex R σ N E hE :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (termEquiv R σ M N e n).toModuleIso)
    (by
      intro n m hnm
      have hm : n + 1 = m := hnm
      subst m
      dsimp only [Tensor.KoszulTensor.complex]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (differential_compatibility R σ M N D E e he n).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorEquivalence.KoszulTensorEquivalence
