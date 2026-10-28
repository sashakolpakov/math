import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.OperatorBracketStability
import OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteTensorSiegelCover

/-! # Bracket Ambient Cover -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketAmbientCover.Construction

noncomputable section

/-! An integral Killing bracket with an adjoint-stable real realization
has a finite ambient Siegel cover modulo its integral automorphisms. -/

open Set _root_.ContinuousLinearMap
open scoped Classical Pointwise OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

theorem integral_bracket_finite_ambient_siegel_cover
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis B ∈ RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m))
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (haB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket (a • B))
    (haK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (a • B)).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g (a • B) = a • B →
      ∀ x y, adjoint g.toContinuousLinearMap ((a • B) x y) =
        (a • B) (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) :
    ∃ F : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)), F.Finite ∧ F ⊆ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b ∧
      ∀ g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L), g • B = B →
        ∃ s ∈ (Ambient.SiegelBracketFiniteness.Construction.ambientSiegelRegion b)⁻¹, ∃ f ∈ F, ∃ δ ∈ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b,
          δ • B = B ∧ g = a⁻¹ * s * f⁻¹ * δ := by
  apply FiniteTensorSiegelCover.Construction.stabilizer_finite_siegel_translates (VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b) B a (Ambient.SiegelBracketFiniteness.Construction.ambientSiegelRegion b)⁻¹
  · intro g _
    exact VolumeOperatorSiegelCover.Construction.volume_operator_siegel_cover b (a * g)
  · apply (Ambient.SiegelBracketFiniteness.Construction.ambient_siegel_integral_brackets_finite b (a • B) haB haK hadj).subset
    rintro w ⟨⟨s, hs, rfl⟩, ⟨γ, hγ, he⟩⟩
    refine ⟨⟨s⁻¹, hs, rfl⟩, ?_⟩
    change Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis (s⁻¹ • (a • B)) ∈
      RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m)
    change γ⁻¹ • B = s⁻¹ • (a • B) at he
    rw [← he]
    exact OperatorBracketStability.Construction.ambientIntegralOperatorGroup_preserves_brackets b γ⁻¹
      ((VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b).inv_mem hγ) B hB

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketAmbientCover.Construction
