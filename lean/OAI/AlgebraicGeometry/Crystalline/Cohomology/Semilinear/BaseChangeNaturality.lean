import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange

/-! # Base Change Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.BaseChangeNaturality.SemilinearBaseChangeNaturality

noncomputable section

/-! # Scalar extension preserves an actual semilinear comparison square -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (σ : R →+* R) (τ : S →+* S)
  (h : ∀ r, τ (algebraMap R S r) = algebraMap R S (σ r))
  (F : M →ₛₗ[σ] M) (G : N →ₛₗ[σ] N) (f : M →ₗ[R] N)

theorem naturality (hf : ∀ x, f (F x) = G (f x)) (z : S ⊗[R] M) :
    f.baseChange S (NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange σ τ h F z) =
      NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange.baseChange σ τ h G (f.baseChange S z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change τ s ⊗ₜ[R] f (F x) = τ s ⊗ₜ[R] G (f x)
    exact congrArg (fun y => τ s ⊗ₜ[R] y) (hf x)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.BaseChangeNaturality.SemilinearBaseChangeNaturality
