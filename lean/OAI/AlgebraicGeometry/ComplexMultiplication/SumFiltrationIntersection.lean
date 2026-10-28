import Mathlib.Algebra.DirectSum.Module

/-! # Sum Filtration Intersection -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SumFiltrationIntersection

noncomputable section

/-! # Two filtrations in an internal direct sum intersect in their common component -/

universe u v w

variable {R : Type u} [Ring R] {V : Type v} [AddCommGroup V] [Module R V]
  {I : Type w} [DecidableEq I]

/-- A coordinate outside the selected summands vanishes. -/
theorem internalSum_coordinate_zero (S : I → Submodule R V) (h : DirectSum.IsInternal S)
    (P : I → Prop) (i : I) (hi : ¬ P i) (x : V) (hx : x ∈ ⨆ j, ⨆ (_ : P j), S j) :
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm x i = 0 := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h
  let π := (DirectSum.component R I (fun j => S j) i).comp e.symm.toLinearMap
  have hker : (⨆ j, ⨆ (_ : P j), S j) ≤ LinearMap.ker π := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro a ha
    change e.symm a i = 0
    exact h.ofBijective_coeLinearMap_of_mem_ne (by
      intro heq
      exact hi (heq ▸ hj)) ha
  exact hker hx

/-- If both selections have only one index in common, their intersection lies in that summand. -/
theorem internalSum_selected_intersection (S : I → Submodule R V)
    (h : DirectSum.IsInternal S) (P Q : I → Prop) (k : I)
    (hk : ∀ i, P i → Q i → i = k) :
    (⨆ i, ⨆ (_ : P i), S i) ⊓ (⨆ i, ⨆ (_ : Q i), S i) ≤ S k := by
  classical
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h
  intro x hx
  have hz : ∀ i, i ≠ k → e.symm x i = 0 := by
    intro i hik
    by_cases hP : P i
    · exact internalSum_coordinate_zero S h Q i (fun hQ => hik (hk i hP hQ)) x hx.2
    · exact internalSum_coordinate_zero S h P i hP x hx.1
  have he : e.symm x = DirectSum.of (fun i => S i) k (e.symm x k) := by
    apply DirectSum.ext_component R
    intro i
    change e.symm x i = (DirectSum.of (fun i => S i) k (e.symm x k)) i
    by_cases hi : i = k
    · subst i
      simp only [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne k i _ hi, hz i hi]
  have hxk : x = (e.symm x k : V) := by
    exact (e.apply_symm_apply x).symm.trans
      ((congrArg (DirectSum.coeLinearMap S) he).trans (DirectSum.coeLinearMap_of S k _))
  exact hxk.symm ▸ (e.symm x k).property

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SumFiltrationIntersection
