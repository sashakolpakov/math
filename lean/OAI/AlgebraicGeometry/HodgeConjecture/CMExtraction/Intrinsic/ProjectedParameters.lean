import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectorRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CoefficientCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters
import OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot

/-! # Projected Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectedParameters

noncomputable section

/-! A projector nonzero on the same theta test selects an auxiliary family.
The fixed-frame dilation and geometric radial construction supply the period,
phase, algebraic root, auxiliary scalar, and Satake witnesses for its exact
character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates.Local
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters.Iwasawa OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices
open scoped Classical TensorProduct

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * Multiplicity.nativeTensorPairing E D.pel.reference v x y))

theorem native_projector_retained_parameters
    (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (u : MpF)
    (i : Fin D.pel.componentCount) (cover : D.domain → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg i cover Θ)
    (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      (CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg i cover Ψ → Ψ = Θ)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (hfull : AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
    (eH : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (heH : eH = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)
    (hBetti : ∀ (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (f : D.sphericalInputs),
      D.activeH1Complex A eH T (ThetaClass.nativeThetaClass D hg Θ f) =
        ThetaClass.nativeThetaClass D hg Θ (D.sphericalWeilComplex T f))
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (haway : ∀ g ∈ D.awayLevel, ∀ p t : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.weil.finite.project (u * D.splitting (1, g) * u⁻¹)).val.mulVec
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t))
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] ParameterChoices.Qbar) (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1))
    (hP : ∀ h, Commute P ((A.cohomologyAction h).baseChange ℂ))
    (hspace : LinearMap.range P ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ)
      (fun h => RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (χ h)))
    (f : D.sphericalInputs) (hne : P (ThetaClass.nativeThetaClass D hg Θ f) ≠ 0)
    (hu : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he)) :
    ∃ (r : Eˣ) (M : ℕ) (ω ζ : ℂ), 0 < M ∧
      ∃ hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace
        (CoefficientCharacter.nativeCoefficientCharacter (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ h) ⊤) ≠ ⊥,
      NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D.pel hg hq hIsogenyQuotient
        (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ
        (CoefficientCharacter.nativeCoefficientCharacter (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ) hχ := by
  let j := RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE
  let χC := CoefficientCharacter.nativeCoefficientCharacter j χ
  let χr := j.toRatAlgHom.comp χ
  let e₀ := RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished
  have hchar : RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χC = ProjectorRestriction.Intrinsic.nativeActiveComplexCharacter D e₀ χr := by
    apply AlgHom.ext
    intro T
    induction T using TensorProduct.inductionOn with
    | add T U hT hU => simp only [map_add, hT, hU]
    | tmul c T => rfl
  have hχ := CoefficientCharacter.native_coefficient_character_occurs D.pel (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
    j χ P hspace (ThetaClass.nativeThetaClass D hg Θ f) hne
  obtain ⟨φ, J, b, hφ, hJ, hneJ⟩ := SphericalCoordinates.native_nonzero_spherical_radial_family D c u hp haway
    (W := ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1) (P.comp (ThetaClass.nativeThetaClass D hg Θ)) f hne
  obtain ⟨r, M, hM, hr, hsplit, ω, ζ, hζ, hframe, hrel, hω, _⟩ :=
    FixedDilation.native_fixed_dilation_from_full_RadialDilation E hRadialDilation hLocalWeil hPoissonAutomorphy D hg hq hμ ιE v hv e he u hu φ hφ
  let Ω := Parameters.ParameterChoices.liftComplexAlgebraic j ω hω.1
  have hΩj : j Ω = ω := Parameters.ParameterChoices.liftComplexAlgebraic_image j ω hω.1
  have hΩ := Parameters.ParameterChoices.unitCircle_all_conjugates j Ω (hΩj.symm ▸ hω)
  let ΘB := (ThetaClass.nativeThetaClass D hg Θ).comp J
  have hδ : ∀ b, ΘB ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j Ω • ΘB b := by
    rw [hΩj]
    exact AuxiliaryClass.native_auxiliary_theta_class_dilation E D hg hμ v hv e he i cover Θ hΘ huniq
      u φ J hJ M ω hframe
  have ht := AuxiliaryBettiHecke.native_auxiliary_theta_class_hecke D hg A eH Θ hBetti c u hp φ J hJ hElementaryDivisors
  rw [heH] at ht
  have hparams := ProjectedParameters.Iwasawa.projected_parameters_of_same_dilation E q hElementaryDivisors hRationalStructure ιE
    (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) v hv
    (Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) (Representatives.Multiplicity.nativeRepresentatives_active E D.pel.reference hμ)
    (Representatives.Multiplicity.nativeRepresentatives_paired E D.pel.reference hg.reference_admissible hμ)
    r hr M hM hsplit Ω ζ hζ (hΩj.symm ▸ hrel) (hΩj.symm ▸ hω) hΩ
    (Spectrum.nativeActiveHeckeActionOver D ℂ A e₀) ΘB hδ ht
    (ProjectorRestriction.Intrinsic.nativeActiveComplexCharacter D e₀ χr) P (ProjectorRestriction.Intrinsic.native_projector_active_commute D A e₀ P hP)
    (ProjectorRestriction.Intrinsic.native_projector_active_space D A e₀ hElementaryDivisors χr P hspace) b hneJ
  refine ⟨r, M, ω, ζ, hM, hχ, ?_⟩
  apply NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.retainedParameters_of_GaloisValuation E D.pel hg hq hIsogenyQuotient
    (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χC hχ
  rw [hchar]
  exact hΩj ▸ hparams

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectedParameters
