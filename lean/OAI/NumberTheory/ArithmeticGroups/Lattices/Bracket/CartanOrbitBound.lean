import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeBracketActionOrbit
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorCartanInvolution
import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitBoundedRepresentatives

/-! # Cartan Orbit Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanOrbitBound.Construction

noncomputable section

/-! On an adjoint-stable Killing bracket orbit, transpose-inverse takes
bounded orbit portions to bounded orbit portions. -/

open _root_.ContinuousLinearMap
open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance cartanOrbit_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance cartanOrbitEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance cartanOrbitEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance cartanOrbitEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance cartanOrbitBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance cartanOrbitBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance cartanOrbitBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

theorem volumeOperatorCartanHom_preserves_bracket_stabilizer
    (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (hg : g • B = B) :
    OperatorCartanInvolution.Construction.volumeOperatorCartanHom g • B = B := by
  have hmem : g.val ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff B g.val).mp hg
  have hinv := (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).inv_mem hmem
  have he := (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff B g.val⁻¹).mpr hinv
  apply (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff B (OperatorCartanInvolution.Construction.operatorCartanHom g.val)).mpr
  exact hadj (ContinuousLinearEquiv.ofUnit g.val⁻¹) he

theorem bracket_cartan_orbit_bound
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (R : ℝ) : ∃ T : ℝ, ∀ g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L),
      ‖g • B‖ ≤ R → ‖OperatorCartanInvolution.Construction.volumeOperatorCartanHom g • B‖ ≤ T := by
  let : LocallyCompactSpace (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits_isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits_isClosed.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  exact ClosedOrbitBoundedRepresentatives.Construction.closed_orbit_stabilizer_preserving_map_bound OperatorCartanInvolution.Construction.volumeOperatorCartanHom
    OperatorCartanInvolution.Construction.volumeOperatorCartanHom_continuous B (VolumeBracketActionOrbit.Construction.volume_operator_orbit_isClosed B hB hK)
    (volumeOperatorCartanHom_preserves_bracket_stabilizer B hadj) R

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanOrbitBound.Construction
