import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedSatake
import OAI.RepresentationTheory.Hecke.GeometricParameters

/-! # Projected Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters.Iwasawa

noncomputable section

/-! A projected auxiliary dilation supplies the complete geometric parameter
conclusion while retaining the Satake witness used to construct it. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

theorem projected_parameters_of_same_dilation
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (q : ℕ) [Fact q.Prime] (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar) (ι : ParameterChoices.Qbar →+* AlgebraicClosure ℚ_[q])
    (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (reps : Finset Gal(E/ℚ)) (ha : (1 : Gal(E/ℚ)) ∈ reps)
    (hp : ∀ τ : Gal(E/ℚ), τ ∈ reps ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1) (M : ℕ) (hM : 0 < M)
    (hsplit : ∀ τ : Gal(E/ℚ), RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι (ιE (τ (r : E))) =
      if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (Ω : ParameterChoices.Qbar) (ζ : ℂ) (hζ : RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ)
    (hrel : (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE Ω) ^ 2 = ζ * ∏ τ ∈ reps,
      ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (hω : RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE Ω))
    (hΩ : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (σ Ω)‖ = 1)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V)
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] V)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE Ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) (P : Module.End ℂ V)
    (hP : ∀ T, Commute P (ρ T))
    (hspace : LinearMap.range P ≤ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T))
    (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (hne : P (Θ b) ≠ 0) :
    RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.ParameterConclusion E q ιE ι v reps r M
      (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE Ω) ζ χ := by
  obtain ⟨ℓ, ρ₁, _, hsat, _, hocc⟩ := ProjectedSatake.Iwasawa.projected_full_satake q hElementaryDivisors ρ Θ M hM
    (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) Ω hΩ hrelation hHecke χ P hP hspace b hne
  exact RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.parameters_of_same_dilation E q ιE ι v reps r M
    (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE Ω) ζ hRationalStructure hv ha hp hr hM hsplit hζ hrel hω
    ρ₁ ℓ hsat χ hocc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters.Iwasawa
