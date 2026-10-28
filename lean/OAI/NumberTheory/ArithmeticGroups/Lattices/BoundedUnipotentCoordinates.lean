import OAI.NumberTheory.ArithmeticGroups.Lattices.OrderedTriangularCompatibility

/-! # Bounded Unipotent Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Bounded matrix coordinates define compact subsets of the
intrinsic unipotent group in an ordered split eigenbasis. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.boundedUnipotentSet (d : KillingSplit.Construction.KillingSplitWeightData B) (c : ℝ) :
    Set (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :=
  {g | ∀ i j, |ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis g.val.val i j| ≤ c}

theorem KillingSplit.Construction.KillingSplitWeightData.boundedUnipotentSet_isCompact (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (c : ℝ) :
    IsCompact (d.boundedUnipotentSet c) := by
  let N := UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)
  let f : N → (Matrix (Fin (Module.finrank ℝ L)) (Fin (Module.finrank ℝ L)) ℝ)ˣ :=
    fun g => ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis g.val
  have hf : Topology.IsClosedEmbedding f :=
    (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis).toHomeomorph.isClosedEmbedding.comp
      (UnipotentBracketGroup.Construction.unipotentBracketUnitGroup_isClosed B d.basis _).isClosedEmbedding_subtypeVal
  have he : d.boundedUnipotentSet c = f ⁻¹' {g |
      UpperUnitriangularMatrices.Construction.IsUpperUnitriangular g.val ∧ ∀ i j, |g.val i j| ≤ c} := by
    ext g
    exact ⟨fun h => ⟨d.ordered_unipotent_matrix_upper hd g, h⟩, fun h => h.2⟩
  rw [he]
  exact hf.isCompact_preimage (UpperUnitriangularMatrices.Construction.bounded_upper_unitriangular_isCompact _ c)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
