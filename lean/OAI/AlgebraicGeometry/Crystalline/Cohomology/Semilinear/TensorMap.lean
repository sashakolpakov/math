import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange

/-! # Tensor Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TensorMap.SemilinearTensorMap

noncomputable section

/-! # Tensoring two compatible semilinear maps over an algebra -/

open scoped TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (σ : R →+* R) (τ : S →+* S)
  (h : ∀ r, τ (algebraMap R S r) = algebraMap R S (σ r))

def map (F : M →ₛₗ[σ] N) : S ⊗[R] M →ₛₗ[τ] S ⊗[R] N where
  toFun := TensorProduct.map (NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.coefficientMap σ τ h) F
  map_add' := map_add _
  map_smul' s z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      change TensorProduct.map (NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.coefficientMap σ τ h) F
        (s • (a ⊗ₜ[R] x)) =
        τ s • TensorProduct.map (NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.coefficientMap σ τ h) F (a ⊗ₜ[R] x)
      simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul]
      change τ (s * a) ⊗ₜ[R] F x = (τ s * τ a) ⊗ₜ[R] F x
      rw [map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem map_tmul (F : M →ₛₗ[σ] N) (a : S) (x : M) :
    SemilinearTensorMap.map σ τ h F (a ⊗ₜ[R] x) = τ a ⊗ₜ[R] F x := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TensorMap.SemilinearTensorMap
