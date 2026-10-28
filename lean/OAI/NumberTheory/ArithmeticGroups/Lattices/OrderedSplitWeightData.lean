import OAI.NumberTheory.ArithmeticGroups.Lattices.DistinctRegularSplitWeights
import Mathlib.Data.Fin.Tuple.Sort

/-! # Ordered Split Weight Data -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Reindexing puts the split weights in decreasing order, while a
regular element separates every distinct weight. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.reindex (d : KillingSplit.Construction.KillingSplitWeightData B)
    (σ : Equiv.Perm (Fin (Module.finrank ℝ L))) : KillingSplit.Construction.KillingSplitWeightData B where
  subspace := d.subspace
  basis := d.basis.reindex σ.symm
  weight i := d.weight (σ i)
  regularElement := d.regularElement
  le_symmetric := d.le_symmetric
  commute := d.commute
  eigenvector i A := by
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    exact d.eigenvector (σ i) A
  regular i := d.regular (σ i)
  opposite i := by
    obtain ⟨j, hj⟩ := d.opposite (σ i)
    exact ⟨σ.symm j, by simpa only [σ.apply_symm_apply] using hj⟩
  centralizer := d.centralizer

theorem OrderedSplitWeightData.Construction.exists_ordered_killing_split_weight_data
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ d : KillingSplit.Construction.KillingSplitWeightData B, Antitone (fun i => d.weight i d.regularElement) ∧
      ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement ↔ d.weight i = d.weight j := by
  obtain ⟨d, hd⟩ := DistinctRegularSplitWeights.Construction.exists_killing_split_weight_data_distinct B hB hK
  let f := fun i => OrderDual.toDual (d.weight i d.regularElement)
  let σ := Tuple.sort f
  refine ⟨d.reindex σ, ?_, fun i j => hd (σ i) (σ j)⟩
  exact Tuple.monotone_sort f

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
