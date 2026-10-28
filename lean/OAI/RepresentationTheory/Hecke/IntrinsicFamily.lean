import OAI.RepresentationTheory.Hecke.AwayPhase
import OAI.RepresentationTheory.Hecke.SphericalCovariance
import OAI.RepresentationTheory.Hecke.CanonicalDilation
import OAI.RepresentationTheory.Hecke.ImageAction
import OAI.RepresentationTheory.Hecke.IntrinsicConclusion
import OAI.RepresentationTheory.Hecke.CanonicalRelations
import OAI.RepresentationTheory.Hecke.RadialComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Intrinsic Family -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicFamily.SphericalActionIntrinsic

noncomputable section

/-! The normalized native cotangent theta form and the GeometricTheta unique
algebraic lift preserve the same whole-family dilation relation. -/

open scoped Classical _root_.Matrix TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local

attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)
  [TopologicalSpace (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

local notation "N" => OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L

theorem native_radial_family
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
      ∃ (M : ℕ) (ω : ℂ), 0 < M ∧ RadialDilation.Cm.algebraicUnitCircle ω ∧
        (∀ e₀ : ℂ, e₀ ^ M = ω → RadialDilation.Cm.algebraicUnitCircle e₀) ∧
        ∀ b, AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ ((RadialDilation.Mem.Realization.dilation q ^ M) b)) =
        ω • AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity.nativeFrameTheta E D.pel.reference hg.reference_admissible hμ v hv e he
          (AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b))
    (f : (N).sphericalInputs) (hf : Θ f ≠ 0) :
    IntrinsicConclusion.SphericalActionIntrinsic.NativeRadialConclusion N u rhoForms eH Θ := by
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
  obtain ⟨M, ω, hM, hω, hroots, hframe⟩ := hfamily φ hφ
  have hd := CanonicalDilation.SphericalActionIntrinsic.canonical_native_dilation E D hg hμ v hv e he c u hu L
    j cover Θ hΘ huniq φ J hJ M ω hframe
  let ρ := ImageAction.SphericalIntrinsic.imageAction (SphericalActionModelInverse.radialAction q .inverseCoset) (Θ.comp J)
    ((N).activeFormsComplex rhoForms eH) hcov'
  refine ⟨φ, hφ, J, ?_, hJ, ⟨b, hb⟩, M, ω, hM, hω, hroots, ρ,
    (fun _ _ => rfl), hcov', hd, ?_⟩
  · intro a b hab
    apply AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding_injective q D.pel.reference.distinguished D.weil u φ hφ
    exact (hJ a).symm.trans ((congrArg Subtype.val hab).trans (hJ b))
  · apply SphericalActionModelInverse.projective_satake_parameters_of_radial_quotient q .inverseCoset
      (Θ.comp J).range ρ (Θ.comp J).rangeRestrict M hM ω (hω.2 ω (minpoly.aeval ℚ ω))
    · exact ImageAction.SphericalIntrinsic.imageAction_intertwines _ _ _ hcov'
    · intro a
      exact Subtype.ext (hd a)

end

end OAI.RepresentationTheory.Hecke.IntrinsicFamily.SphericalActionIntrinsic
