import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketCartanRealization
import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeNormalizedCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeBracketActionOrbit

/-! # Self Adjoint Bracket Realization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SelfAdjointBracketRealization.Construction

noncomputable section

/-! Every real Killing bracket has an adjoint-stable realization by a
volume-preserving change of coordinates on its original space. -/

open _root_.ContinuousLinearMap
open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

theorem exists_volume_selfAdjoint_bracket_realization
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L), ContinuousBracketConstraints.Construction.IsContinuousLieBracket (a • B) ∧
      (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (a • B)).Nondegenerate ∧
      ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g (a • B) = a • B →
        ∀ x y, adjoint g.toContinuousLinearMap ((a • B) x y) =
          (a • B) (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  obtain ⟨e, he⟩ := KillingBracketCartanRealization.Construction.exists_killing_selfAdjoint_coordinate_automorphism B hB hK
  obtain ⟨f, hf, hfe⟩ := VolumeNormalizedCoordinates.Construction.exists_volume_normalized_coordinates e
  let a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) := ⟨f.toUnit, hf⟩
  have hC : a • B = Positive.Killing.Construction.continuousBracketTransport f B := by ext x y; rfl
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [hC]
    exact Positive.Killing.Construction.continuousBracketTransport_isLie f B hB
  · rw [hC]
    exact Positive.Killing.Construction.continuousBracketTransport_killing_nondegenerate f B hK
  · rw [hC]
    apply KillingBracketCartanRealization.Construction.transported_bracket_adjoint_stable B f
    intro g hg
    obtain ⟨h, hh, hadj⟩ := he g hg
    exact ⟨h, hh, by rwa [hfe]⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SelfAdjointBracketRealization.Construction
