import OAI.NumberTheory.PadicHodge.GeometricThetaParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

/-! # Opposite Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositePurity.Intrinsic

noncomputable section

section

/-! Retain FrobeniusSlope's original five parameter witnesses while constructing
its comparison at the opposite place and applying full ExtremeSlopes there. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.GeometricThetaParameters.CM.ExtremeSlopesAdapter.Geometric
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters.ParameterChoices

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (rCM : Eˣ) (M : ℕ) (ω ζ : ℂ)

theorem retained_parameter_comparison_at
    (χ : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (Ω Ζ a e : ParameterChoices.Qbar) (β : Fin 3 → ParameterChoices.Qbarˣ)
    (hd : NumberTheory.PadicHodge.ThetaArithmetic.FrobeniusSlope.ParameterData E q ιE
      (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) v
      (Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference) rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ) Ω Ζ a e β)
    (hunit : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (σ a)‖ = 1)
    (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q]) :
    NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) ι χ hχ a := by
  obtain ⟨_, _, ha, _, he, _, _, hβ, hχβ, _⟩ := hd
  intro fullSide hCentralAction f hf j hCubicRelation O hGeometricComparison P ℓ _ hℓq
  exact NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Model.comparison_from_retained_root D hg hq hIsogenyQuotient A hA fullSide hCentralAction j
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) a
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_sq q j.complexClosure)
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_image q j.complexClosure) ha (hunit 1)
    β (he ▸ hβ) χ hχ hχβ hCubicRelation O (@hGeometricComparison) P ℓ hℓq

theorem retained_parameters_opposite_purity
    (χ : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ) :
    ∃ Ω Ζ a e β,
      NumberTheory.PadicHodge.ThetaArithmetic.FrobeniusSlope.ParameterData E q ιE
        (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) v
        (Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference) rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ) Ω Ζ a e β ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (σ a)‖ = 1) ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q (Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D) (σ a) =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2)) ∧
      NumberTheory.PadicHodge.ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.RootPurityAt E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
        (Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D)
        (fun σ => v.val (ParameterChoices.restriction E ιE σ)) (-3 / 2) χ hχ a := by
  obtain ⟨Ω, Ζ, a, e, β, hd, hunit, _, hgal, _⟩ := h
  have hopp : ∀ σ : Gal(ParameterChoices.Qbar/ℚ),
      RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q (Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D) (σ a) =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) :=
    Intrinsic.OppositeParameters.ParameterChoices.native_opposite_root_valuation E ιE D v a hgal
  refine ⟨Ω, Ζ, a, e, β, hd, hunit, hopp, ?_⟩
  apply NumberTheory.PadicHodge.ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.root_family_add_purity E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D) (fun σ => v.val (ParameterChoices.restriction E ιE σ))
    (-3 / 2) χ hχ a hd.2.2.1 (Or.inl rfl)
  · intro σ
    exact (NumberTheory.PadicHodge.GeometricRootValuation.CM.ExtremeSlopesAdapter.Geometric.native_value_eq_canonical q _ (σ a)).symm.trans (hopp σ)
  · exact retained_parameter_comparison_at E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ
      χ hχ Ω Ζ a e β hd hunit (Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D)

end

/-! Apply the full FrobeniusSlope comparison and ExtremeSlopes purity to the retained
parameters after the integral ordinary-point polynomial has been transported
to the actual rational Hecke realization. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.NumberTheory.PadicHodge.GeometricThetaParameters.CM.ExtremeSlopesAdapter.Geometric
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters.ParameterChoices
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (v : Multiplicity.Odd.Sign E) (rCM : Eˣ) (M : ℕ) (ω ζ : ℂ)

theorem retained_opposite_polynomial_purity
    (χ : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hretained : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ)
    (side : Fin s → Bool) (hside : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished side)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D)
    (hpoly : HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).specialFiber.scheme)
      (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
        (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i)) = 0)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (P : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D hg hq j) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ Ω Ζ a e β,
      NumberTheory.PadicHodge.ThetaArithmetic.FrobeniusSlope.ParameterData E q ιE
        (ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) v
        (Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference) rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ) Ω Ζ a e β ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j.complexClosure (σ a)‖ = 1) ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (j.iota (σ a)) =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2)) ∧
      ∃ b : ParameterChoices.Qbar, b ≠ 0 ∧ (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
        (∀ i, NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i) =
          NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) b a i) ∧
        NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.ComparisonHodgeForced (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
          (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
          (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
          (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) b a ℓ ∧
        NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure
          (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
          (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
          (fun σ => 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) / 3) := by
  obtain ⟨Ω, Ζ, a, e, β, hd, hunit, _, hgal, _⟩ := hretained
  have hu : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j.complexClosure (σ a)‖ = 1 := by
    simpa only [hcomplex] using hunit
  have hv : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (j.iota (σ a)) =
      (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
    intro σ
    rw [hopposite, ← NumberTheory.PadicHodge.GeometricRootValuation.CM.ExtremeSlopesAdapter.Geometric.native_value_eq_canonical]
    exact Intrinsic.OppositeParameters.ParameterChoices.native_opposite_root_valuation E ιE D v a hgal σ
  refine ⟨Ω, Ζ, a, e, β, hd, hu, hv, ?_⟩
  apply NumberTheory.PadicHodge.GeometricIntrinsicBridge.CM.ExtremeSlopesAdapter.Geometric.native_parameter_comparison_add_purity D hg hq hIsogenyQuotient A hA side j
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) a χ hχ P ℓ
    (fun σ => v.val (ParameterChoices.restriction E ιE σ)) (-3 / 2) hd.2.2.1 (Or.inl rfl) hv
  obtain ⟨_, _, ha, _, he, _, _, hβ, hχβ, _⟩ := hd
  obtain ⟨b, hb, hcentral, hvalues⟩ := NumberTheory.PadicHodge.ThetaParameters.FrobeniusSlope.central_values_from_retained_root
    D hg hq hIsogenyQuotient A hA side hside j.complexClosure
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) a
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_image q j.complexClosure) ha β
    (by simpa only [hcomplex] using (he ▸ hβ)) χ hχ
    (by simpa only [hcomplex] using hχβ)
  refine ⟨b, hb, hcentral, hvalues, ?_⟩
  exact NumberTheory.PadicHodge.IntrinsicComparison.FrobeniusSlopeIntrinsic.comparison_forced_from_full_GeometricComparison (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure
    j.complexClosure j.iota (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
    (@hGeometricComparison) j.closure_compatibility.symm ℓ hℓq (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side) hpoly
    (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
    (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.native_character_occurs D hg hq hIsogenyQuotient A hA j χ hχ)
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) b a
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_sq q j.complexClosure)
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_image q j.complexClosure) (hu 1) hcentral hvalues

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositePurity.Intrinsic
