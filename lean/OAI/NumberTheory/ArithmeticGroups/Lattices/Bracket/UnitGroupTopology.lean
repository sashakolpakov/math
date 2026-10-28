import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv

/-! # Unit Group Topology -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitGroupTopology.Construction

noncomputable section

/-! The finite-dimensional bracket automorphism group is locally
compact and second countable. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem bracketUnitGroup_locallyCompact (B : L →L[ℝ] L →L[ℝ] L) :
    LocallyCompactSpace (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) := by
  let : LocallyCompactSpace (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  exact (UnipotentBracketGroup.Construction.continuousBracketUnitGroup_isClosed B).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem bracketUnitGroup_secondCountable (B : L →L[ℝ] L →L[ℝ] L) :
    SecondCountableTopology (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) := by
  let : SecondCountableTopology (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  exact (UnipotentBracketGroup.Construction.continuousBracketUnitGroup_isClosed B).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitGroupTopology.Construction
