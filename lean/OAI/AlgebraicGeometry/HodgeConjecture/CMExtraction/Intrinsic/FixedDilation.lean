import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives
import OAI.RepresentationTheory.Hecke.RadialDilation.Realized
import OAI.RepresentationTheory.Hecke.RadialComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedAuxiliaryFamily

/-! # Fixed Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedDilation

noncomputable section

/-! A single scalar, power, auxiliary input and phase give RadialDilation for
the entire constructed native period family, retaining exact splitting. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.Realized.Realization
open scoped Classical _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_fixed_dilation_from_full_RadialDilation
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
    (u : MpF) (hu : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he)) :
      ∀ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ),
        0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        RepresentationTheory.Hecke.RadialDilation.Realized.Realization.RadialDilationConclusion E (Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r q M
          (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
          (FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he)
          (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ) := by
  have hfin := FixedAuxiliaryFamily.native_fixed_auxiliary_radial_family E D hLocalWeil hg hq ιE v e he u hu
  intro φ hφ
  obtain ⟨r, M, γ, Uq, ξ, hM, hr, hγ, hsplit, hj, hξ, hUq, hf⟩ := hfin φ hφ
  let P := D.pel.reference
  let z₀ := PeriodDomain.Multiplicity.nativeOrigin E P hg.reference_admissible
  let Z₀ := PeriodFamily.Multiplicity.nativePeriod E P hg.reference_admissible hμ v hv e he z₀
  let Θ := FamilyTheta.Multiplicity.nativeFrameTheta E P hg.reference_admissible hμ v hv e he
  have hdet := (FamilyTheta.native_theta_scalar_for_period hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z₀).2.1
  have hdet' := Representatives.Multiplicity.native_halfDet_identity E P hg.reference_admissible hμ v r
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀) hdet
  have hact : P.embeddings P.distinguished (r : E) = ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E) :=
    RingHom.congr_fun hμ (r : E)
  have hp : ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3), Θ (D.weil.finiteAction γ f) =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀ * (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-(-1 : ℤ))) • Θ f := by
    intro f
    simp only [neg_neg, zpow_one]
    exact hact ▸ FamilyTheta.native_family_theta_covariance hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z₀ f
  have hout := hRadialDilation E
    v hv (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl)
    (Representatives.Multiplicity.nativeRepresentatives E P) (Representatives.Multiplicity.nativeRepresentatives_active E P hμ)
    (Representatives.Multiplicity.nativeRepresentatives_paired E P hg.reference_admissible hμ) r hr q M hM
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) ({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} → Fin 2 → ℂ)
    ((AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q P.distinguished D.weil u φ).comp (RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q).toLinearMap)
    (hj.comp (RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q).injective) Θ
    (D.weil.finiteAction γ).toLinearMap (RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.statementDilation q) Uq (RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.statementDilation_formula q) hUq ξ hξ hf
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀) hdet' (-1) (Or.inr rfl) hp
  refine ⟨r, M, hM, hr, hsplit, ?_⟩
  obtain ⟨ω, ζ, hζ, hrel, heq, hω, hroots⟩ := hout.2
  refine ⟨ω, ζ, hζ, ?_, ?_, hω, hroots⟩
  · intro b
    have h := hrel ((RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q).symm b)
    change Θ (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q P.distinguished D.weil u φ
        (RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q ((RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.statementDilation q ^ M) ((RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q).symm b)))) =
      ω • Θ (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q P.distinguished D.weil u φ
        (RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q ((RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.radialComparison q).symm b))) at h
    rw [RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic.normalized_dilation_power_intertwining, LinearEquiv.apply_symm_apply,
      Radial.Dilation.dilationEquiv_pow_apply] at h
    exact h
  · simpa only [neg_one_mul] using heq

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedDilation
