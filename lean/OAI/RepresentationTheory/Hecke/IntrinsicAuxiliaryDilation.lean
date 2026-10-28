import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives
import OAI.RepresentationTheory.Hecke.RadialDilation.Realized
import OAI.RepresentationTheory.Hecke.RadialComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryFiniteFamily

/-! # Intrinsic Auxiliary Dilation -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicAuxiliaryDilation.SphericalActionIntrinsic

noncomputable section

/-! A single scalar, power, auxiliary input and phase give RadialDilation for
the entire constructed native period family, retaining exact splitting. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.Realized.Realization
open scoped Classical _root_.Matrix

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

theorem native_auxiliary_dilation_from_full_RadialDilation
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hRadialDilation : SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    ∃ (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF), AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u ∧
      ∀ φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ),
        0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        RadialDilation.Realized.Realization.RadialDilationConclusion E (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r q M
          (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he)
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ) := by
  obtain ⟨e, he, u, hlocal, hfin⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryFiniteFamily.native_finite_auxiliary_radial_family E D hLocalWeil hg hq ιE v
  refine ⟨e, he, u, hlocal, ?_⟩
  intro φ hφ
  obtain ⟨r, M, γ, Uq, ξ, hM, hr, hγ, hsplit, hj, hξ, hUq, hf⟩ := hfin φ hφ
  let P := D.pel.reference
  let z₀ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E P hg.reference_admissible
  let Z₀ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodFamily.Multiplicity.nativePeriod E P hg.reference_admissible hμ v hv e he z₀
  let Θ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E P hg.reference_admissible hμ v hv e he
  have hdet := (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.native_theta_scalar_for_period hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z₀).2.1
  have hdet' := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.native_halfDet_identity E P hg.reference_admissible hμ v r
    (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀) hdet
  have hact : P.embeddings P.distinguished (r : E) = AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E) :=
    RingHom.congr_fun hμ (r : E)
  have hp : ∀ f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3), Θ (D.weil.finiteAction γ f) =
      ((Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀ * (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-(-1 : ℤ))) • Θ f := by
    intro f
    simp only [neg_neg, zpow_one]
    exact hact ▸ AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.native_family_theta_covariance hPoissonAutomorphy E D hg hμ v hv r hr e he γ hγ z₀ f
  have hout := hRadialDilation E
    v hv (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E P) (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives_active E P hμ)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives_paired E P hg.reference_admissible hμ) r hr q M hM
    (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) ({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} → Fin 2 → ℂ)
    ((AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q P.distinguished D.weil u φ).comp (RadialComparison.SphericalActionIntrinsic.radialComparison q).toLinearMap)
    (hj.comp (RadialComparison.SphericalActionIntrinsic.radialComparison q).injective) Θ
    (D.weil.finiteAction γ).toLinearMap (RadialComparison.SphericalActionIntrinsic.statementDilation q) Uq (RadialComparison.SphericalActionIntrinsic.statementDilation_formula q) hUq ξ hξ hf
    (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀) hdet' (-1) (Or.inr rfl) hp
  refine ⟨r, M, hM, hr, hsplit, ?_⟩
  obtain ⟨ω, ζ, hζ, hrel, heq, hω, hroots⟩ := hout.2
  refine ⟨ω, ζ, hζ, ?_, ?_, hω, hroots⟩
  · intro b
    have h := hrel ((RadialComparison.SphericalActionIntrinsic.radialComparison q).symm b)
    change Θ (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q P.distinguished D.weil u φ
        (RadialComparison.SphericalActionIntrinsic.radialComparison q ((RadialComparison.SphericalActionIntrinsic.statementDilation q ^ M) ((RadialComparison.SphericalActionIntrinsic.radialComparison q).symm b)))) =
      ω • Θ (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q P.distinguished D.weil u φ
        (RadialComparison.SphericalActionIntrinsic.radialComparison q ((RadialComparison.SphericalActionIntrinsic.radialComparison q).symm b))) at h
    rw [RadialComparison.SphericalActionIntrinsic.normalized_dilation_power_intertwining, LinearEquiv.apply_symm_apply,
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation.dilationEquiv_pow_apply] at h
    exact h
  · simpa only [neg_one_mul] using heq

end

end OAI.RepresentationTheory.Hecke.IntrinsicAuxiliaryDilation.SphericalActionIntrinsic
