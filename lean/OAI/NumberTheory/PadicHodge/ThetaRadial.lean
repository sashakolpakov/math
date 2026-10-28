import OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot
import OAI.RepresentationTheory.Hecke.GeometricFamily
import OAI.RepresentationTheory.Hecke.Theta

/-! # Theta Radial -/

namespace OAI.NumberTheory.PadicHodge.ThetaRadial.FrobeniusSlope

noncomputable section

/-! One radial inclusion and CM dilation witness throughout the arithmetic and Betti comparison. -/

open scoped Classical _root_.Matrix TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]

open OAI.RepresentationTheory.Hecke.Theta.CentralConstraintIntrinsic

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

def RadialWithFrobenius : Prop :=
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
    ∀ (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
      (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace (χ h) ⊤) ≠ ⊥),
      (∃ x : ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D.pel, x ∈ (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J).range ∧ x ≠ 0 ∧
        ∀ h, RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h x =
          RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ h • x) →
      FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D.pel hg hq hIsogenyQuotient
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χ hχ

theorem radialWithFrobenius_of_signs
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rhoForms h))
    (heH : eH = RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.pel.reference.distinguished)
    (hμ : D.pel.reference.μ = E.val.toRingHom) (hv : v.val 1 = true)
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (h : RepresentationTheory.Hecke.GeometricFamily.GaloisValuation.RadialWithSigns E D u ιE v rhoForms eH Θ) :
    RadialWithFrobenius E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns⟩ := h
  have hbetti := RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial_satake D hg P hq hIsogenyQuotient A hA coeff rhoForms hrho eH heH
    Θ J M hM ω hω hcov hd
  refine ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns,
    ⟨hbetti, RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualCentralConclusion_of_satake D.pel hg hq hIsogenyQuotient _ hfull _ M ω hbetti⟩, ?_⟩
  intro χ hχ hocc
  apply FrobeniusSlopeThetaRoot.Conclusion.retainedParameters_of_GaloisValuation E D.pel hg hq hIsogenyQuotient
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χ hχ
  exact RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.parameters_of_same_dilation E q ιE
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false))
    v (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r M ω ζ hRationalStructure hv
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives_active E D.pel.reference hμ)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives_paired E D.pel.reference hg.reference_admissible hμ)
    hr hM hsplit hζ hprod hω
    (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D.pel (AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
    (RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic.actualBettiRadial D hg Θ J) hbetti (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ) hocc

theorem radialWithFrobenius_to_signs
    (h : RadialWithFrobenius E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ) :
    RepresentationTheory.Hecke.GeometricFamily.GaloisValuation.RadialWithSigns E D u ιE v rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns, _⟩ := h
  exact ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, hsigns⟩

theorem radialWithFrobenius_to_actual
    (h : RadialWithFrobenius E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ) :
    RepresentationTheory.Hecke.Theta.CentralConstraintIntrinsic.ActualRadialConclusion D u hg A coeff rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, _, M, hM, _, _, ω, _, _, _,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, _, hbetti, _⟩ := h
  exact ⟨φ, hφ, J, hinj, hJ, hn, M, ω, hM, hω, hroots, ρ, hρ, hcov, hd, hSatake, hbetti⟩

end

end OAI.NumberTheory.PadicHodge.ThetaRadial.FrobeniusSlope
