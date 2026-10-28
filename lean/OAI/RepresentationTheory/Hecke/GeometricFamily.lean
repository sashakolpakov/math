import OAI.RepresentationTheory.Hecke.GeometricParameters
import OAI.RepresentationTheory.Hecke.IntrinsicDatum

/-! # Geometric Family -/

namespace OAI.RepresentationTheory.Hecke.GeometricFamily.GaloisValuation

noncomputable section

/-! A nonzero value of the canonical algebraic theta map selects an auxiliary
radial family. Its dilation, period, phase, and root witnesses are retained
through the Galois valuation calculation. -/

open scoped Classical _root_.Matrix TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]

/-- The complete native radial output with its original scalar-product witness,
before the arithmetic specialization. -/
def RadialWitness
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (u : MpF) (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) : Prop :=
  ∃ φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 ∧
  ∃ J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs,
    Function.Injective J ∧
    (∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) ∧
    (∃ b, Θ (J b) ≠ 0) ∧
  ∃ (r : Eˣ) (M : ℕ), 0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
    (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
  ∃ ω ζ : ℂ, RadialDilation.Cm.finitePhase ζ ∧
    ω ^ 2 = ζ * ∏ τ ∈ AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference,
      AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
    RadialDilation.Cm.algebraicUnitCircle ω ∧
    (∀ e₀ : ℂ, e₀ ^ M = ω → RadialDilation.Cm.algebraicUnitCircle e₀) ∧
  ∃ ρ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range,
    (∀ h y, (ρ h y).val = D.activeFormsComplex rhoForms eH h y.val) ∧
    (∀ h b, Θ (J (SphericalActionModelInverse.radialAction q .inverseCoset h b)) =
      D.activeFormsComplex rhoForms eH h (Θ (J b))) ∧
    (∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b)) ∧
    SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset (V := (Θ.comp J).range)
      ρ (Θ.comp J).rangeRestrict M ω

/-- The same scalar-product witness with signed valuations for every occurring character. -/
def RadialWithSigns
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (u : MpF) (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) : Prop :=
  ∃ φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 ∧
  ∃ J : SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs,
    Function.Injective J ∧
    (∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) ∧
    (∃ b, Θ (J b) ≠ 0) ∧
  ∃ (r : Eˣ) (M : ℕ), 0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
    (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
  ∃ ω ζ : ℂ, RadialDilation.Cm.finitePhase ζ ∧
    ω ^ 2 = ζ * ∏ τ ∈ AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference,
      AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
    RadialDilation.Cm.algebraicUnitCircle ω ∧
    (∀ e₀ : ℂ, e₀ ^ M = ω → RadialDilation.Cm.algebraicUnitCircle e₀) ∧
  ∃ ρ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range,
    (∀ h y, (ρ h y).val = D.activeFormsComplex rhoForms eH h y.val) ∧
    (∀ h b, Θ (J (SphericalActionModelInverse.radialAction q .inverseCoset h b)) =
      D.activeFormsComplex rhoForms eH h (Θ (J b))) ∧
    (∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b)) ∧
    SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset (V := (Θ.comp J).range)
      ρ (Θ.comp J).rangeRestrict M ω ∧
    (∀ χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ,
      (∃ x : (Θ.comp J).range, x ∈ LinearMap.range (Θ.comp J).rangeRestrict ∧ x ≠ 0 ∧
        ∀ h, ρ h x = χ h • x) →
      GeometricParameters.GaloisValuation.ParameterConclusion E q ιE
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) v
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r M ω ζ χ)

theorem radialWithSigns_to_native
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (u : MpF) (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (h : RadialWithSigns E D u ιE v rhoForms eH Θ) :
    IntrinsicConclusion.SphericalActionIntrinsic.NativeRadialConclusion D u rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, _, M, hM, _, _, ω, _, _, _, hω, hroots,
    ρ, hρ, hcov, hd, hSatake, _⟩ := h
  exact ⟨φ, hφ, J, hinj, hJ, hn, M, ω, hM, hω, hroots, ρ, hρ, hcov, hd, hSatake⟩

/-- Arithmetic specialization is separate from the geometric family construction. -/
theorem radialWitness_add_signs
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    {u : MpF} (h : RadialWitness E D u ιE v rhoForms eH Θ) :
    RadialWithSigns E D u ιE v rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake⟩ := h
  refine ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, ?_⟩
  intro χ hχ
  exact GeometricParameters.GaloisValuation.parameters_of_same_dilation (V := (Θ.comp J).range) E q ιE
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false))
    v (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r M ω ζ hRationalStructure hv
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives_active E D.pel.reference hμ)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives_paired E D.pel.reference hg.reference_admissible hμ)
    hr hM hsplit hζ hprod hω ρ (Θ.comp J).rangeRestrict hSatake χ hχ

variable (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
  [TopologicalSpace (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

local notation "N" => OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L

theorem native_radial_family_with_witness
    (hSphericalAction : GaloisValuationIntrinsic.Intrinsic.SphericalAction.Proposition.{1})
    (j : Fin D.pel.componentCount)
    (cover : (N).domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : (N).sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (N).IsCanonicalThetaLift hg j cover Θ)
    (huniq : ∀ Ψ, (N).IsCanonicalThetaLift hg j cover Ψ → Ψ = Θ)
    (hcov : ∀ (h : SphericalActionModelInverse.SphericalAlgebra q) (f : (N).sphericalInputs),
      (N).activeFormsComplex rhoForms eH h (Θ f) = Θ ((N).sphericalWeilComplex h f))
    (hfamily : ∀ φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ), 0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        RadialDilation.Realized.Realization.RadialDilationConclusion E (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r q M
          (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he)
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ))
    (f : (N).sphericalInputs) (hf : Θ f ≠ 0) :
    RadialWitness E N u ιE v rhoForms eH Θ := by
  have hs : (N).splitting.comp (MonoidHom.inl (Theta.Geometric.SphericalGU.Spherical.SL3 q) _) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u := by
    ext g
    exact IntrinsicDatum.SphericalActionIntrinsic.nativeSplitting_local E D hg hμ v hv e he c u hu g
  have hp : ∀ g : Theta.Geometric.SphericalGU.Spherical.SL3 q, (N).weil.finite.project ((N).splitting (g, 1)) =
      ((N).weil.finite.project u)⁻¹ * RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (Weil.Local.Generators.Construction.leviSymplectic
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) *
            (N).weil.finite.project u := by
    intro g
    exact (congrArg D.weil.finite.project
      (IntrinsicDatum.SphericalActionIntrinsic.nativeSplitting_local E D hg hμ v hv e he c u hu g)).trans
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateDualHecke.Local.coordinateDualLift_projection q c D.pel.reference.distinguished D.weil u g)
  obtain ⟨φ, J, b, hφ, hJ, hb⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates.native_nonzero_spherical_radial_family N c u hp
    (fun g _ p t => AwayPhase.SphericalActionIntrinsic.nativeDatum_away_fixes_phase E D hg hμ v hv e he c u hu L g p t) Θ f hf
  have hcov' : ∀ h b, (Θ.comp J) (SphericalActionModelInverse.radialAction q .inverseCoset h b) =
      (N).activeFormsComplex rhoForms eH h ((Θ.comp J) b) := by
    intro h b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcov,
      SphericalCovariance.ActionIntrinsic.native_spherical_auxiliary_complex N c u hs φ J hJ (SphericalActionModelInverse.cartanInput q)]
    rfl
  obtain ⟨r, M, hM, hr, hsplit, ω, ζ, hζ, hframe, hprod, hω, hroots⟩ := hfamily φ hφ
  have hd := CanonicalDilation.SphericalActionIntrinsic.canonical_native_dilation E D hg hμ v hv e he c u hu L
    j cover Θ hΘ huniq φ J hJ M ω hframe
  let ρ := ImageAction.SphericalIntrinsic.imageAction (SphericalActionModelInverse.radialAction q .inverseCoset) (Θ.comp J)
    ((N).activeFormsComplex rhoForms eH) hcov'
  have hSatake : SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset (V := (Θ.comp J).range)
      ρ (Θ.comp J).rangeRestrict M ω := by
    apply hSphericalAction q .inverseCoset ↥(Θ.comp J).range ρ (Θ.comp J).rangeRestrict
      M hM ω (hω.2 ω (minpoly.aeval ℚ ω))
    · exact ImageAction.SphericalIntrinsic.imageAction_intertwines _ _ _ hcov'
    · intro a
      exact Subtype.ext (hd a)
  refine ⟨φ, hφ, J, ?_, hJ, ⟨b, hb⟩, r, M, hM, hr, hsplit,
    ω, ζ, hζ, hprod, hω, hroots, ρ, (fun _ _ => rfl), hcov', hd, hSatake⟩
  · intro a b hab
    apply AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding_injective q D.pel.reference.distinguished D.weil u φ hφ
    exact (hJ a).symm.trans ((congrArg Subtype.val hab).trans (hJ b))

theorem native_radial_family_with_signs
    (hSphericalAction : GaloisValuationIntrinsic.Intrinsic.SphericalAction.Proposition.{1})
    (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (j : Fin D.pel.componentCount)
    (cover : (N).domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : (N).sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : (N).IsCanonicalThetaLift hg j cover Θ)
    (huniq : ∀ Ψ, (N).IsCanonicalThetaLift hg j cover Ψ → Ψ = Θ)
    (hcov : ∀ (h : SphericalActionModelInverse.SphericalAlgebra q) (f : (N).sphericalInputs),
      (N).activeFormsComplex rhoForms eH h (Θ f) = Θ ((N).sphericalWeilComplex h f))
    (hfamily : ∀ φ : RadialDilation.TestSections.Realization.lcCompactSpace (RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ), 0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        RadialDilation.Realized.Realization.RadialDilationConclusion E (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r q M
          (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he)
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ))
    (f : (N).sphericalInputs) (hf : Θ f ≠ 0) :
    RadialWithSigns E N u ιE v rhoForms eH Θ := by
  apply radialWitness_add_signs E N hg hμ ιE v hv hRationalStructure rhoForms eH Θ
  exact native_radial_family_with_witness E D hg hμ ιE v hv e he c u hu L hSphericalAction
    j cover rhoForms eH Θ hΘ huniq hcov hfamily f hf

end

end OAI.RepresentationTheory.Hecke.GeometricFamily.GaloisValuation
