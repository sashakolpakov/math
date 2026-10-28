import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.OperatorSiegelData
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelTensorWeights
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanOrbitBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteTensorSiegelCover

/-! # Siegel Bracket Finiteness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelBracketFiniteness.Construction

noncomputable section

/-! The concrete ambient Siegel region meets an adjoint-stable Killing
bracket orbit in only finitely many integral bracket tensors. -/

open Set _root_.ContinuousLinearMap
open scoped Classical Pointwise OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance ambientFinite_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance ambientFiniteEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance ambientFiniteEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance ambientFiniteEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance ambientFiniteBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance ambientFiniteBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance ambientFiniteBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

def ambientSiegelRegion {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
  OperatorSiegelData.Construction.ambientSiegelUnipotent b * OperatorSiegelData.Construction.ambientSiegelDiagonal b * OperatorSiegelData.Construction.ambientSiegelCompact

theorem ambient_siegel_integral_brackets_finite {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) :
    (((fun g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) => g • B) '' ambientSiegelRegion b) ∩
      (Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis ⁻¹' Integral.RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m))).Finite := by
  let : LocallyCompactSpace (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology (L →L[ℝ] L)ˣ := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits_isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : SecondCountableTopology (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
    VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits_isClosed.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  obtain ⟨D, D₂, hD, hD₂, hconj, hconj₂⟩ := OperatorSiegelData.Construction.ambientSiegel_compact_conjugates b
    (OperatorSiegelData.Construction.ambientSiegelUnipotent b) (OperatorSiegelData.Construction.ambientSiegelUnipotent_isCompact b) (OperatorSiegelData.Construction.ambientSiegelUnipotent_upper b)
  exact FiniteTensorSiegelCover.Construction.siegel_reflection_integral_points_finite (Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis) B
    (VolumeBracketActionOrbit.Construction.volume_operator_orbit_isClosed B hB hK) OperatorCartanInvolution.Construction.volumeOperatorCartanHom OperatorCartanInvolution.Construction.volumeOperatorCartanHom_continuous
    (Bracket.CartanOrbitBound.Construction.volumeOperatorCartanHom_preserves_bracket_stabilizer B hadj)
    (OperatorSiegelData.Construction.ambientSiegelUnipotent b) (OperatorSiegelData.Construction.ambientSiegelDiagonal b) OperatorSiegelData.Construction.ambientSiegelCompact D D₂
    (OperatorSiegelData.Construction.ambientSiegelUnipotent_isCompact b) OperatorSiegelData.Construction.ambientSiegelCompact_isCompact hD hD₂ hconj hconj₂
    (OperatorSiegelData.Construction.ambientSiegelDiagonal_cartan b) OperatorSiegelData.Construction.ambientSiegelCompact_cartan (SiegelTensorWeights.Construction.ambientSiegelTensorWeight b)
    (SiegelTensorWeights.Construction.ambientSiegelTensorWeight_action b)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelBracketFiniteness.Construction
