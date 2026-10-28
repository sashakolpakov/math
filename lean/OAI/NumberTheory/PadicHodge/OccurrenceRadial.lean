import OAI.NumberTheory.PadicHodge.ThetaRadial
import OAI.RepresentationTheory.Hecke.OccurrenceRadial

/-! # Occurrence Radial -/

namespace OAI.NumberTheory.PadicHodge.OccurrenceRadial.FrobeniusSlope

noncomputable section

/-! Extend the existing radial witnesses by the original forms-occurrence
premise. The accepted parameter/root/comparison result is applied once. -/

open scoped Classical _root_.Matrix TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]

open OAI.RepresentationTheory.Hecke.OccurrenceRadial.CentralConstraintIntrinsic

variable
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (u : MpF) (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (coeff : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s → AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
    (hfull : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
    (rhoForms : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)

/-- The added clauses use the original forms-image representation. -/
def FaithfulApplications
    (J : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (r : Eˣ) (M : ℕ) (ω ζ : ℂ) : Prop :=
  Function.Bijective (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.formsImageToBetti D hg Θ J) ∧
  (∃ b, RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J b ≠ 0) ∧
  RepresentationTheory.Hecke.ThetaOccurrence.CentralConstraintIntrinsic.FormsCentralConclusion D hg A coeff Θ J ρ M ω ∧
  ∀ (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace (χ h) ⊤) ≠ ⊥),
    (∃ y : (Θ.comp J).range, y ≠ 0 ∧ ∀ h, ρ h y = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ h • y) →
    FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D.pel hg hq hIsogenyQuotient
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χ hχ

def FaithfulRadial : Prop :=
  ∃ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 ∧
  ∃ J : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs,
    Function.Injective J ∧
    (∀ b, (J b).val = AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b) ∧
    (∃ b, Θ (J b) ≠ 0) ∧
  ∃ (r : Eˣ) (M : ℕ), 0 < M ∧ (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
    (∀ τ : Gal(E/ℚ), Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
        if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
  ∃ ω ζ : ℂ, RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ ∧
    ω ^ 2 = ζ * ∏ τ ∈ AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference,
      AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
    RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ω ∧
    (∀ e₀ : ℂ, e₀ ^ M = ω → RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀) ∧
  ∃ ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range,
    (∀ h y, (ρ h y).val = D.activeFormsComplex rhoForms eH h y.val) ∧
    (∀ h b, Θ (J (RepresentationTheory.Hecke.SphericalActionModelInverse.radialAction q .inverseCoset h b)) =
      D.activeFormsComplex rhoForms eH h (Θ (J b))) ∧
    (∀ b, Θ (J ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b)) = ω • Θ (J b)) ∧
    RepresentationTheory.Hecke.SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset (V := (Θ.comp J).range)
      ρ (Θ.comp J).rangeRestrict M ω ∧
    (∀ χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ,
      (∃ x : (Θ.comp J).range, x ∈ LinearMap.range (Θ.comp J).rangeRestrict ∧ x ≠ 0 ∧
        ∀ h, ρ h x = χ h • x) →
      RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.ParameterConclusion E q ιE
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) v
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r M ω ζ χ) ∧
    RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.ActualBettiConclusion D.pel hg (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
      (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J) M ω ∧
    (∀ (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
      (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace (χ h) ⊤) ≠ ⊥),
      (∃ x : ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D.pel, x ∈ (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J).range ∧ x ≠ 0 ∧
        ∀ h, RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h x =
          RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ h • x) →
      FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D.pel hg hq hIsogenyQuotient
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χ hχ) ∧
    FaithfulApplications E D ιE v hg hq hIsogenyQuotient A coeff hfull Θ J ρ r M ω ζ

variable
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h))
    (heH : eH = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (huniq : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Ψ → Ψ = Θ)

include P hA hrho heH hcover hΘ huniq in
/-- Consume the existing application; do not reconstruct its parameter witnesses. -/
theorem faithfulApplications_of_original
    (J : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (hn : ∃ b, Θ (J b) ≠ 0)
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (hρ : ∀ h y, (ρ h y).val = D.activeFormsComplex rhoForms eH h y.val)
    (r : Eˣ) (M : ℕ) (ω ζ : ℂ)
    (hbetti : RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.ActualBettiConclusion D.pel hg (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
      (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J) M ω)
    (hresults : ∀ (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
      (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace (χ h) ⊤) ≠ ⊥),
      (∃ x : ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D.pel, x ∈ (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J).range ∧ x ≠ 0 ∧
        ∀ h, RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h x =
          RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ h • x) →
      FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D.pel hg hq hIsogenyQuotient
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χ hχ) :
    FaithfulApplications E D ιE v hg hq hIsogenyQuotient A coeff hfull Θ J ρ r M ω ζ := by
  have occurs (χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
      (hforms : ∃ y : (Θ.comp J).range, y ≠ 0 ∧ ∀ h, ρ h y = χ h • y) :
      ∃ x : ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D.pel, x ∈ (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J).range ∧ x ≠ 0 ∧
        ∀ h, RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h x = χ h • x := by
    obtain ⟨y, hy, heigen⟩ := hforms
    exact RepresentationTheory.Hecke.ThetaOccurrence.CentralConstraintIntrinsic.canonicalTheta_occurs_betti_of_forms D hg P hq hIsogenyQuotient A hA coeff rhoForms hrho eH heH
      Θ j X component cover hcover hΘ huniq J χ y hy (by
        intro h
        exact (hρ h y).symm.trans (congrArg Subtype.val (heigen h)))
  refine ⟨RepresentationTheory.Hecke.ThetaNonvanishing.CentralConstraintIntrinsic.canonicalTheta_formsImageToBetti_bijective D hg Θ j X component cover hcover hΘ huniq J,
    RepresentationTheory.Hecke.ThetaNonvanishing.CentralConstraintIntrinsic.canonicalTheta_actualBettiRadial_nonzero D hg Θ j X component cover hcover hΘ huniq J hn,
    ?_, ?_⟩
  · intro side hCentralAction hCommuting χ hχ hforms
    exact hbetti.2 side hCentralAction hCommuting χ hχ (occurs (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ) hforms)
  · intro χ hχ hforms
    exact hresults χ hχ (occurs (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ) hforms)

include P hA hrho heH hcover hΘ huniq in
theorem faithfulRadial_of_original
    (h : ThetaRadial.FrobeniusSlope.RadialWithFrobenius E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ) :
    FaithfulRadial E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns, hbetti, hresults⟩ := h
  exact ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns, hbetti, hresults,
    faithfulApplications_of_original E D ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ
      P hA hrho heH j X component cover hcover hΘ huniq J hn ρ hρ r M ω ζ hbetti hresults⟩

theorem faithfulRadial_to_original
    (h : FaithfulRadial E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ) :
    ThetaRadial.FrobeniusSlope.RadialWithFrobenius E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns, hbetti, hresults, _⟩ := h
  exact ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns, hbetti, hresults⟩

theorem faithfulRadial_to_CentralConstraint
    (h : FaithfulRadial E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ) :
    RepresentationTheory.Hecke.OccurrenceRadial.CentralConstraintIntrinsic.FaithfulRadialConclusion D u hg A coeff rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, _, M, hM, _, _, ω, _, _, _,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, _, hbetti, _, hfaithful⟩ := h
  exact ⟨φ, hφ, J, hinj, hJ, hn, M, ω, hM, hω, hroots, ρ, hρ, hcov, hd, hSatake, hbetti,
    hfaithful.1, hfaithful.2.1, hfaithful.2.2.1⟩

end

end OAI.NumberTheory.PadicHodge.OccurrenceRadial.FrobeniusSlope
