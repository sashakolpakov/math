import OAI.RepresentationTheory.Theta.Adelic.TensorProjective

/-! # Restricted Tensor Expansion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedTensorExpansion.CM

noncomputable section

/-! Every element of the actual restricted tensor space is a finite
linear combination of restricted pure tensors. -/

open scoped Classical TensorProduct
open Filter
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable {I : Type*} {S : I → Type*}
  [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (vac : ∀ i, S i)

theorem expansion (x : RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.restrictedTensor vac) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (f : Fin n → ∀ i, S i)
      (hf : ∀ j, ∀ᶠ i in cofinite, f j i = vac i),
      x = ∑ j, c j • RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure vac (f j) (hf j) := by
  obtain ⟨n, c, t, ht⟩ := Submodule.mem_span_set'.mp x.property
  choose f hf he using fun j => (t j).property
  refine ⟨n, c, f, hf, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  exact ht.symm.trans (Finset.sum_congr rfl (fun j _ => congrArg (c j • ·) (he j).symm))

variable {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (ρ : ∀ i, G i →* (S i ≃ₗ[ℂ] S i))
  (hunramified : ∀ᶠ i in cofinite, ∀ g ∈ K i, ρ i g (vac i) = vac i)

include hunramified in
theorem transformed_restricted (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)
    (f : ∀ i, S i) (hf : ∀ᶠ i in cofinite, f i = vac i) :
    ∀ᶠ i in cofinite, ρ i (g i) (f i) = vac i := by
  filter_upwards [hunramified, g.property, hf] with i hi hg hfi
  rw [hfi]
  exact hi (g i) hg

theorem action_pure (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)
    (f : ∀ i, S i) (hf : ∀ᶠ i in cofinite, f i = vac i) :
    RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action vac K ρ hunramified g (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure vac f hf) =
      RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure vac (fun i => ρ i (g i) (f i)) (transformed_restricted vac K ρ hunramified g f hf) := by
  apply Subtype.ext
  exact RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.fullAction_pure K ρ g f

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedTensorExpansion.CM
