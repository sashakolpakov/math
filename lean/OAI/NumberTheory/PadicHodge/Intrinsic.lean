import OAI.NumberTheory.PadicHodge.IntrinsicComparison
import OAI.NumberTheory.PadicHodge.IntrinsicModel
import OAI.NumberTheory.PadicHodge.IntrinsicDilation
import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

/-! # Intrinsic -/

namespace OAI.NumberTheory.PadicHodge.Intrinsic.FrobeniusSlopeIntrinsic

noncomputable section

/-! FrobeniusSlope on the actual TateComparison Albanese and Hecke summands. Full RadialDilation,
CubicRelation and GeometricComparison inputs are instantiated at their natural source data.
Native CentralConstraint, SphericalAction and Commuting are applied through their proved declarations. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.IntrinsicDilation.FrobeniusSlopeIntrinsic

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem native_forced_frobenius_and_slope
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (fullSide : Fin s → Bool)
    (hCentralAction : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide)
    (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (B : IntrinsicDilation.FrobeniusSlopeIntrinsic.DilationData q (ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D))
    (hRadialDilation : IntrinsicDilation.FrobeniusSlopeIntrinsic.RadialDilationInput.{0, 0})
    (c : RepresentationTheory.Hecke.SphericalActionModelInverse.ActingConvention)
    (hGeometricTheta : ∀ h b, B.radialTheta (RepresentationTheory.Hecke.SphericalActionModelInverse.radialAction q c h b) =
      RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A h (B.radialTheta b))
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hΘχ : ∃ v : ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D, v ∈ LinearMap.range B.radialTheta ∧ v ≠ 0 ∧
      ∀ h, RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A h v = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ h • v)
    (hCubicRelation : IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.CubicRelationInput.{0, 0, 0, 0})
    (O : IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.OrdinaryData q
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).specialFiber.scheme)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished)))
    (hGeometricComparison : GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.left
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ ω ζ : ℂ,
      RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ ∧
      (∀ b, B.radialTheta ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ B.M) b) = ω • B.radialTheta b) ∧
      ω ^ 2 = ζ * ∏ τ ∈ B.reps,
        (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv B.E τ (B.unit : B.E)) ^
          (-3 * B.d τ) ∧
      RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ B.M = ω → RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀) ∧
      ∃ e₀ : ℂ, e₀ ≠ 0 ∧ e₀ ^ B.M = ω ∧
      ∃ r b e : AlgebraicClosure ℚ,
        r ^ 2 = (q : AlgebraicClosure ℚ) ∧
        j.complexClosure r = (Real.sqrt (q : ℝ) : ℂ) ∧ b ≠ 0 ∧
        j.complexClosure e = (RepresentationTheory.Hecke.SphericalActionModelInverse.parameterForConvention c e₀)⁻¹ ∧
        (∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1) ∧
        (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
          (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b e i) ∧
        IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
          (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
          (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b e ℓ := by
  obtain ⟨_harch, ω, ζ, hζ, hrel, hprod, hω, hroots⟩ := B.full_dilation hRadialDilation
  have hωnorm : ‖ω‖ = 1 := hω.2 ω (minpoly.aeval ℚ ω)
  have hSphericalAction := RepresentationTheory.Hecke.SphericalActionModelInverse.projective_satake_parameters_of_radial_quotient
    q c (ℂ ⊗[ℚ] RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.RationalBetti D) (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveAction D A) B.radialTheta
    B.M B.hM ω hωnorm hGeometricTheta (fun b => by
      simpa only [AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation.dilationEquiv_pow_apply] using hrel b)
  have h67 : letI := RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
      RepresentationTheory.Hecke.CentralConstraint.Construction.CommutingInput (fun h => RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h) := by
    let := RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
    intro hc
    exact LinearAlgebra.Endomorphisms.Commuting.Construction.commuting_family_structure _ hc
  obtain ⟨e₀, he₀, hroot, r, b, e, hr, hrC, hb, he, hcentral, hvalues⟩ :=
    IntrinsicParameters.FrobeniusSlopeIntrinsic.parameters_from_native_CentralConstraint D hg hq hIsogenyQuotient A hTateComparison fullSide hCentralAction c B.radialTheta
      B.M ω hSphericalAction h67 j.complexClosure χ hχ hΘχ
  refine ⟨ω, ζ, hζ, hrel, hprod, hω, hroots, e₀, he₀, hroot,
    r, b, e, hr, hrC, hb, he, hcentral, hvalues, ?_⟩
  have hp := IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.specialized_polynomial_from_full_CubicRelation (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
    (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
    (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2)
    (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) hCubicRelation O
  exact IntrinsicComparison.FrobeniusSlopeIntrinsic.comparison_forced_from_full_GeometricComparison (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
    j.fieldInClosure j.complexClosure j.iota (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
    (@hGeometricComparison) j.closure_compatibility.symm ℓ hℓq (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide) hp
    (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
    (IntrinsicModel.FrobeniusSlopeIntrinsic.native_character_occurs D hg hq hIsogenyQuotient A hTateComparison j χ hχ)
    r b e hr hrC (he.symm ▸ IntrinsicParameters.FrobeniusSlopeIntrinsic.norm_of_dilation_root (hroots e₀ hroot)) hcentral hvalues

end

end OAI.NumberTheory.PadicHodge.Intrinsic.FrobeniusSlopeIntrinsic
