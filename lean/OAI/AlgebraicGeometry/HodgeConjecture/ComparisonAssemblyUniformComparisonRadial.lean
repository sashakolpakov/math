import OAI.AlgebraicGeometry.HodgeConjecture.ComparisonConclusion
import OAI.NumberTheory.PadicHodge.OccurrenceRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositePurity

/-! # Comparison Assembly Uniform Comparison Radial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ComparisonAssemblyUniformComparisonRadial.CMExtractionIntrinsic

noncomputable section

/-! Keep the original radial family and its single set of parameters while
applying the full comparison to every occurring character of that family. -/

open scoped Classical _root_.Matrix TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (u : MpF) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
  (coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →
    AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
  (hfull : AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff))
  (rhoForms : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
  (eH : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
  (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
  (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)

def UniformComparisonApplications
    (J : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (r : Eˣ) (M : ℕ) (ω ζ : ℂ) : Prop :=
  ∀ (χ : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace
      (χ h) ⊤) ≠ ⊥),
    (∃ y : (Θ.comp J).range, y ≠ 0 ∧ ∀ h, ρ h y = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D.pel χ h • y) →
    ∀ (proj : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D.pel hg hq j)
      (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q →
      ComparisonConclusion.CMExtractionIntrinsic.FullComparisonConclusion E D.pel hg hq hIsogenyQuotient (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
        hfull ιE v r M ω ζ χ hχ side j proj ℓ

theorem uniform_comparison_of_faithful_applications
    (hside : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D.pel (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
      D.pel.reference.distinguished side)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q)
        (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).specialFiber.scheme)
      (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction
        (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j)
        (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D.pel hg hq hIsogenyQuotient
          (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull j)
        (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D.pel (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) side i)) = 0)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (J : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (r : Eˣ) (M : ℕ) (ω ζ : ℂ)
    (h : NumberTheory.PadicHodge.OccurrenceRadial.FrobeniusSlope.FaithfulApplications E D ιE v hg hq hIsogenyQuotient
      A coeff hfull Θ J ρ r M ω ζ) :
    UniformComparisonApplications E D ιE v hg hq hIsogenyQuotient A coeff hfull Θ side j J ρ r M ω ζ := by
  intro χ hχ hforms proj ℓ _ hℓq
  exact CMExtraction.OppositePurity.Intrinsic.retained_opposite_polynomial_purity E D.pel hg hq hIsogenyQuotient
    (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull ιE v r M ω ζ χ hχ
    (h.2.2.2 χ hχ hforms) side hside j hcomplex hopposite hpoly hGeometricComparison proj ℓ hℓq

def UniformRadial : Prop :=
  NumberTheory.PadicHodge.OccurrenceRadial.FrobeniusSlope.FaithfulRadial E D u ιE v hg hq hIsogenyQuotient A coeff hfull rhoForms eH Θ ∧
  ∀ (J : RepresentationTheory.Hecke.SphericalActionModelInverse.Radial q →ₗ[ℂ] D.sphericalInputs)
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Θ.comp J).range)
    (r : Eˣ) (M : ℕ) (ω ζ : ℂ),
    NumberTheory.PadicHodge.OccurrenceRadial.FrobeniusSlope.FaithfulApplications E D ιE v hg hq hIsogenyQuotient
      A coeff hfull Θ J ρ r M ω ζ →
    UniformComparisonApplications E D ιE v hg hq hIsogenyQuotient A coeff hfull Θ side j J ρ r M ω ζ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ComparisonAssemblyUniformComparisonRadial.CMExtractionIntrinsic
