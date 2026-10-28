import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarExtension

/-! # Scalar Equiv Transport Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarEquivTransportNaturality.FilteredBaseChangeTransport

noncomputable section

section

/-! Filtered scalar extension transports through actual linear equivalences on both ends. -/

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S]
  {M N U V : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid U] [AddCommMonoid V]
  [Module R M] [Module R N] [Module S U] [Module S V]

theorem inverse_map (e : M ≃ₗ[R] N) (P : Submodule R M) (Q : Submodule R N)
    (h : P.map e.toLinearMap = Q) :
    (Q.baseChange S).map (e.symm.baseChange R S _ _).toLinearMap = P.baseChange S := by
  change (Q.baseChange S).map (e.symm.toLinearMap.baseChange S) = _
  rw [← ScalarExtension.ScalarExtensionRanges.map, (Submodule.map_symm_eq_iff e).mpr h]

def equiv (e : M ≃ₗ[R] N) (f : S ⊗[R] M ≃ₗ[S] U) (g : U ≃ₗ[S] V) : S ⊗[R] N ≃ₗ[S] V :=
  (e.symm.baseChange R S _ _).trans (f.trans g)

theorem filtration (e : M ≃ₗ[R] N) (f : S ⊗[R] M ≃ₗ[S] U) (g : U ≃ₗ[S] V)
    (P : Submodule R M) (Q : Submodule R N) (T : Submodule S U) (W : Submodule S V)
    (he : P.map e.toLinearMap = Q) (hf : (P.baseChange S).map f.toLinearMap = T)
    (hg : T.map g.toLinearMap = W) :
    (Q.baseChange S).map (equiv S e f g).toLinearMap = W := by
  change (Q.baseChange S).map (g.toLinearMap.comp
    (f.toLinearMap.comp (e.symm.baseChange R S _ _).toLinearMap)) = W
  rw [Submodule.map_comp, Submodule.map_comp, inverse_map S e P Q he, hf, hg]

end

/-! Transporting a scalar comparison through actual coordinate equivalences preserves a proved naturality square. -/

open scoped TensorProduct

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M₁ M₂ N₁ N₂ U₁ U₂ V₁ V₂ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
  [AddCommGroup U₁] [AddCommGroup U₂] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂]
  [Module S U₁] [Module S U₂] [Module S V₁] [Module S V₂]

theorem naturality (e₁ : M₁ ≃ₗ[R] N₁) (e₂ : M₂ ≃ₗ[R] N₂)
    (f₁ : S ⊗[R] M₁ ≃ₗ[S] U₁) (f₂ : S ⊗[R] M₂ ≃ₗ[S] U₂)
    (g₁ : U₁ ≃ₗ[S] V₁) (g₂ : U₂ ≃ₗ[S] V₂)
    (a : M₂ →ₗ[R] M₁) (a' : N₂ →ₗ[R] N₁) (b : U₂ →ₗ[S] U₁) (b' : V₂ →ₗ[S] V₁)
    (he : ∀ x, e₁ (a x) = a' (e₂ x))
    (hf : ∀ x, f₁ (a.baseChange S x) = b (f₂ x))
    (hg : ∀ x, g₁ (b x) = b' (g₂ x)) (x : S ⊗[R] N₂) :
    equiv S e₁ f₁ g₁ (a'.baseChange S x) = b' (equiv S e₂ f₂ g₂ x) := by
  have hi : e₁.symm.toLinearMap.comp a' = a.comp e₂.symm.toLinearMap := by
    apply LinearMap.ext
    intro y
    apply e₁.injective
    exact (e₁.apply_symm_apply (a' y)).trans
      ((congrArg a' (e₂.apply_symm_apply y)).symm.trans (he (e₂.symm y)).symm)
  have hs := congrArg (fun k : N₂ →ₗ[R] M₁ => k.baseChange S) hi
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hs
  have hx := LinearMap.congr_fun hs x
  exact (congrArg (fun z => g₁ (f₁ z)) hx).trans
    ((congrArg g₁ (hf (e₂.symm.toLinearMap.baseChange S x))).trans
      (hg (f₂ (e₂.symm.toLinearMap.baseChange S x))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarEquivTransportNaturality.FilteredBaseChangeTransport
