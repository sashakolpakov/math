import OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedExtension
import Mathlib.Algebra.BigOperators.Finprod

/-! # Family Locally Finite Sum -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FamilyLocallyFiniteSum.Godement

noncomputable section

/-! Pointwise finite sums of actual stalk families agree locally with
ordinary finite sums. No infinite additivity of a sheaf map is required. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped BigOperators

variable {X : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℂ) X} {ι : Type*}

def stalkFamilySum (t : ι → (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op ⊤)) :
    (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op ⊤) := fun x => ∑ᶠ i, t i x

theorem stalkFamilySum_restrict (t : ι → (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.obj (op ⊤))
    (W : Opens X) (s : Finset ι)
    (ht : ∀ i, i ∉ s → ∀ x : (⊤ : Opens X), x.val ∈ W → t i x = 0) :
    (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.map (homOfLE (show W ≤ ⊤ from le_top)).op (stalkFamilySum t) =
      ∑ i ∈ s, (HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F).obj.map (homOfLE (show W ≤ ⊤ from le_top)).op (t i) := by
  classical
  funext x
  change (∑ᶠ i, t i ⟨x.val, trivial⟩) = (∑ i ∈ s, fun y : W => t i ⟨y.val, trivial⟩) x
  rw [Finset.sum_apply]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  exact hi (ht i his ⟨x.val, trivial⟩ x.property)

end

end OAI.AlgebraicGeometry.Comparison.Betti.FamilyLocallyFiniteSum.Godement
