import OAI.RepresentationTheory.Hecke.GeometricFamily
import OAI.RepresentationTheory.Hecke.Parameters
import OAI.RepresentationTheory.Hecke.IntrinsicDatum

/-! # Family -/

namespace OAI.RepresentationTheory.Hecke.Family.GaloisValuation

noncomputable section

/-! A nonzero value of the canonical algebraic theta map selects one
auxiliary radial family. Its full r/M/omega/phase witness is retained all
the way through SphericalAction and the Galois valuation calculation. -/

open scoped Classical _root_.Matrix TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

open OAI.RepresentationTheory.Hecke.GeometricFamily.GaloisValuation
attribute [local instance] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]

/-- Arithmetic specialization is separate from the geometric family construction. -/
theorem radialWitness_add_signs
    (D : Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices.Qbar) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (rhoForms : Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (eH : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    {u : MpF} (h : GeometricFamily.GaloisValuation.RadialWitness E D u ιE v rhoForms eH Θ) :
    GeometricFamily.GaloisValuation.RadialWithSigns E D u ιE v rhoForms eH Θ := by
  obtain ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake⟩ := h
  refine ⟨φ, hφ, J, hinj, hJ, hn, r, M, hM, hr, hsplit, ω, ζ, hζ, hprod,
    hω, hroots, ρ, hρ, hcov, hd, hSatake, ?_⟩
  intro χ hχ
  exact Parameters.GaloisValuation.parameters_of_same_dilation (V := (Θ.comp J).range) E q ιE
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false))
    v (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.pel.reference) r M ω ζ hv
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

theorem native_radial_family_with_signs
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
    GeometricFamily.GaloisValuation.RadialWithSigns E N u ιE v rhoForms eH Θ := by
  apply radialWitness_add_signs E N hg hμ ιE v hv rhoForms eH Θ
  exact GeometricFamily.GaloisValuation.native_radial_family_with_witness E D hg hμ ιE v hv e he c u hu L
    SphericalActionModelInverse.projective_satake_parameters_of_radial_quotient
    j cover rhoForms eH Θ hΘ huniq hcov hfamily f hf

end

end OAI.RepresentationTheory.Hecke.Family.GaloisValuation
