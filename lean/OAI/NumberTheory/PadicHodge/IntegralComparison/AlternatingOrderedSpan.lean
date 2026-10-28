import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Alternating Ordered Span -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlternatingOrderedSpan

noncomputable section

/-!
# IntegralComparison: ordered values span the values of an alternating map
-/

universe u v w z

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]
  (M : Type w) [AddCommGroup M] [Module R M]
  (N : Type z) [AddCommGroup N] [Module R N] [Module A N]
  (σ : Type*) [LinearOrder σ] (n : ℕ)
  (f : AlternatingMap R M N (Fin n)) (x : σ → M)

def ordered (s : Set.powersetCard σ n) : N :=
  f (fun j => x (Set.powersetCard.ofFinEmbEquiv.symm s j))

theorem mem_span (v : Fin n → σ) :
    f (x ∘ v) ∈ Submodule.span A (Set.range (ordered R M N σ n f x)) := by
  classical
  by_cases hv : Function.Injective v
  · have hcard : (Finset.image v Finset.univ).card = n :=
      (Finset.card_image_of_injective Finset.univ hv).trans (Finset.card_fin n)
    let s : Set.powersetCard σ n := ⟨Finset.image v Finset.univ, hcard⟩
    let π : Equiv.Perm (Fin n) := (Finset.orderIsoOfFin (Finset.image v Finset.univ) hcard).toEquiv.trans
      ((Set.equivOfEq Fintype.coe_image_univ).trans (Equiv.ofInjective v hv).symm)
    have he : v ∘ π = fun j => Set.powersetCard.ofFinEmbEquiv.symm s j := by
      funext j
      simp only [Function.comp_apply, π, Equiv.trans_apply]
      simp only [Equiv.apply_ofInjective_symm]
      rfl
    have hs : f ((x ∘ v) ∘ π) ∈ Submodule.span A (Set.range (ordered R M N σ n f x)) := by
      rw [Function.comp_assoc, he]
      exact Submodule.subset_span ⟨s, rfl⟩
    rw [f.map_congr_perm (x ∘ v) π]
    exact (Submodule.span A (Set.range (ordered R M N σ n f x))).toAddSubgroup.zsmul_mem hs (π.sign : ℤ)
  · have hz : f (x ∘ v) = 0 := f.map_eq_zero_of_not_injective _ (fun h => hv h.of_comp)
    rw [hz]
    exact Submodule.zero_mem _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlternatingOrderedSpan
