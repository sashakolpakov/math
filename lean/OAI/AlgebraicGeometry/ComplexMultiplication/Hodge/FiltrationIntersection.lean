import OAI.AlgebraicGeometry.ComplexMultiplication.SumFiltrationIntersection
import OAI.Analysis.HodgeTheory.Decomposition.Core

/-! # Filtration Intersection -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.FiltrationIntersection

noncomputable section

/-! # The genuine bidegree decomposition identifies the middle Hodge intersection -/

open OAI.Analysis.HodgeTheory.Decomposition.Core.Constructions

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- In degree `2p`, the two conjugate filtrations intersect in precisely the `(p,p)` summand. -/
theorem bidegree_filtration_intersection (p : ℕ)
    (S : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree (2 * p) → Submodule ℂ V) (h : DirectSum.IsInternal S)
    (c : V →ₛₗ[starRingEnd ℂ] V) (hc : Function.Involutive c)
    (hS : ∀ i x, x ∈ S i → c x ∈ S (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i))
    (x : V) (hx : x ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.1), S i)
    (hcx : c x ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.1), S i) :
    x ∈ S ⟨(p, p), by omega⟩ := by
  classical
  have hmap : (⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.1), S i) ≤
      (⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.2), S i).comap c := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro a ha
    change c a ∈ ⨆ j, ⨆ (_ : (p : ℤ) ≤ j.val.2), S j
    apply Submodule.mem_iSup_of_mem (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i)
    apply Submodule.mem_iSup_of_mem hi
    exact hS i a ha
  have hx' : x ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.2), S i := by
    have hh := hmap hcx
    change c (c x) ∈ ⨆ i, ⨆ (_ : (p : ℤ) ≤ i.val.2), S i at hh
    rwa [hc x] at hh
  apply SumFiltrationIntersection.internalSum_selected_intersection S h
    (fun i => (p : ℤ) ≤ i.val.1) (fun i => (p : ℤ) ≤ i.val.2)
      ⟨(p, p), by omega⟩ ?_ ⟨hx, hx'⟩
  intro i h₁ h₂
  apply Subtype.ext
  apply Prod.ext
  · have hi := i.property
    dsimp at hi h₁ h₂ ⊢
    omega
  · have hi := i.property
    dsimp at hi h₁ h₂ ⊢
    omega

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.FiltrationIntersection
