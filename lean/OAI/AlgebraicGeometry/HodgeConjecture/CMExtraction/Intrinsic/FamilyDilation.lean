import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives
import OAI.RepresentationTheory.Hecke.RadialDilation.Realized

/-! # Family Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyDilation

noncomputable section

/-! A single scalar, power, auxiliary input and phase give RadialDilation for
the entire constructed native period family, retaining exact splitting. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.Realized.Realization
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_family_dilation_with_local_action
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    ∃ (r : Eˣ) (M : ℕ)
      (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF),
      0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
        (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
          if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
      RepresentationTheory.Hecke.RadialDilation.Realized.Realization.RadialDilationConclusion E (Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r q M
        (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
        (FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he)
        (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q D.pel.reference.distinguished D.weil u) ∧
      FiniteDilation.NativeFiniteCoordinateIdentity E D e u := by
  obtain ⟨r, M, e, γ, u, Uq, ξ, hM, hr, he, hγ, hsplit, hj, hξ, hUq, hf, hlocal⟩ :=
    FiniteDilation.native_finite_radial_dilation_with_local_action E D hLocalWeil hg hq ιE v
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
  have hout := RepresentationTheory.Hecke.RadialDilation.Cm.algebraic_dilation_relation E hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy
    v hv (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl)
    (Representatives.Multiplicity.nativeRepresentatives E P) (Representatives.Multiplicity.nativeRepresentatives_active E P hμ)
    (Representatives.Multiplicity.nativeRepresentatives_paired E P hg.reference_admissible hμ) r hr q M hM
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) ({z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} → Fin 2 → ℂ)
    (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q P.distinguished D.weil u) hj Θ
    (D.weil.finiteAction γ).toLinearMap (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) Uq (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation_apply q) hUq ξ hξ hf
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z₀) hdet' (-1) (Or.inr rfl) hp
  refine ⟨r, M, e, he, u, hM, hr, hsplit, ?_, hlocal⟩
  simpa only [RepresentationTheory.Hecke.RadialDilation.Realized.Realization.RadialDilationConclusion, neg_one_mul, Θ, P] using hout.2

theorem native_family_dilation
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    ∃ (r : Eˣ) (M : ℕ)
      (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
      (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
        Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))
      (u : MpF),
      0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
      (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
        (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
          if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
      RepresentationTheory.Hecke.RadialDilation.Realized.Realization.RadialDilationConclusion E (Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r q M
        (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
        (FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he)
        (RepresentationTheory.Hecke.RadialDilation.ConcreteFinite.Realization.coordinateRadialEmbedding q D.pel.reference.distinguished D.weil u) := by
  obtain ⟨r, M, e, he, u, hM, hr, hsplit, hradial, _⟩ :=
    native_family_dilation_with_local_action E hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy D hg hq hμ ιE v hv
  exact ⟨r, M, e, he, u, hM, hr, hsplit, hradial⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyDilation
