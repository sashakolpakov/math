import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ConjugationAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketAmbientCover
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.SiegelQRBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRTranslateClosed

/-! # Bracket QR Finite Cover -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketQRFiniteCover.Construction

noncomputable section

/-! The finite arithmetic ambient cover yields a finite cover by
closed QR intersection pieces in the self-adjoint bracket stabilizer. -/

open _root_.ContinuousLinearMap
open scoped Classical OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

theorem integral_bracket_finite_qr_cover
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hint : Bilinear.DiagonalCoordinates.Construction.continuousBilinearCoordinates b.toBasis B ∈ RealCoordinates.Construction.integralRealCoordinates (Fin m × Fin m × Fin m))
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (haB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket (a • B))
    (haK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (a • B)).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g (a • B) = a • B →
      ∀ x y, adjoint g.toContinuousLinearMap ((a • B) x y) =
        (a • B) (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) :
    ∃ F : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)), F.Finite ∧
      ∀ g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B), ∃ f ∈ F,
        ∃ c ∈ QRTranslateClosed.Construction.qrTranslateIntersection b (a • B) (f⁻¹ * a⁻¹).val (Real.log 2) 1,
        ∃ γ ∈ Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup b (a • B) haK a, g = c * γ := by
  obtain ⟨F, hF, _, hCover⟩ := BracketAmbientCover.Construction.integral_bracket_finite_ambient_siegel_cover b B hint a haB haK hadj
  refine ⟨F, hF, fun g => ?_⟩
  obtain ⟨s, hs, f, hf, δ, hδ, hδB, he⟩ := hCover
    (Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom (a • B) haK a g) (Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom_smul B a haK g)
  let γ : UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B) :=
    ⟨(a * δ * a⁻¹).val, Bracket.ConjugationAction.Construction.volume_conjugate_bracket_unit B a δ hδB⟩
  have hγV : Bracket.ConjugationAction.Construction.bracketVolumeHom (a • B) haK γ = a * δ * a⁻¹ := by
    apply Subtype.ext
    rfl
  have hγ : γ ∈ Bracket.ConjugationAction.Construction.conjugatedIntegralBracketSubgroup b (a • B) haK a := by
    change Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom (a • B) haK a γ ∈ VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b
    rw [Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom_apply, hγV]
    have heq : a⁻¹ * (a * δ * a⁻¹) * a = δ := by group
    rw [heq]
    exact hδ
  rw [Bracket.ConjugationAction.Construction.conjugatedBracketVolumeHom_apply] at he
  have hG : Bracket.ConjugationAction.Construction.bracketVolumeHom (a • B) haK g = s * (f⁻¹ * a⁻¹) * (a * δ * a⁻¹) := by
    calc
      Bracket.ConjugationAction.Construction.bracketVolumeHom (a • B) haK g = a * (a⁻¹ * Bracket.ConjugationAction.Construction.bracketVolumeHom (a • B) haK g * a) * a⁻¹ := by group
      _ = a * (a⁻¹ * s * f⁻¹ * δ) * a⁻¹ := by rw [he]
      _ = _ := by group
  let c := g * γ⁻¹
  have hcV : Bracket.ConjugationAction.Construction.bracketVolumeHom (a • B) haK c = s * (f⁻¹ * a⁻¹) := by
    change Bracket.ConjugationAction.Construction.bracketVolumeHom (a • B) haK (g * γ⁻¹) = _
    rw [map_mul, map_inv, hγV, hG]
    group
  have hc : c.val = s.val * (f⁻¹ * a⁻¹).val :=
    congrArg (fun h : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) => h.val) hcV
  refine ⟨f, hf, c, ?_, γ, hγ, ?_⟩
  · rw [QRTranslateClosed.Construction.qrTranslateIntersection_eq]
    exact ⟨s.val, Ambient.SiegelQRBounds.Construction.ambient_siegel_inverse_qr_bounds b s hs, hc⟩
  · dsimp only [c]
    group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.BracketQRFiniteCover.Construction
