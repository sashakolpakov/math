import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectedParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositePurity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AuxiliaryClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectorRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CoefficientCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FixedDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters
import OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot

/-! # Projector Polynomial Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectorPolynomialPurity

noncomputable section

/-! Full projector comparison and Frobenius purity for a coefficient character
selected by the same nonzero projected theta test. The ordinary polynomial
is expressed on the exact integral model and Hecke realization. -/

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

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

theorem native_projector_polynomial_purity
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
      (FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (side : Fin s → Bool)
    (hside : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D.pel (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) D.pel.reference.distinguished side)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j).specialFiber.scheme)
      (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j)
        (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull j)
        (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D.pel (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) side i)) = 0)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (proj : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D.pel hg hq j)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j) j.fieldInClosure j.complexClosure
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull j) proj χ
      (fun τ => 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE τ)) : ℚ) * (-3 / 2) / 3) := by
  obtain ⟨r, M, ω, ζ, _, hχ, hret⟩ := ProjectedParameters.native_projector_retained_parameters E D hg hμ v hv e he
    hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure ιE u i cover Θ hΘ huniq hq hIsogenyQuotient A coeff hfull
    eH heH hBetti c hp haway hElementaryDivisors χ P hP hspace f hne hu
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpurity⟩ :=
    OppositePurity.Intrinsic.retained_opposite_polynomial_purity E D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
      hfull ιE v r M ω ζ (CoefficientCharacter.nativeCoefficientCharacter (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ)
      hχ hret side hside j hcomplex hopposite hpoly hGeometricComparison proj ℓ hℓq
  have hlift : NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D.pel hg (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
      j.complexClosure (CoefficientCharacter.nativeCoefficientCharacter (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ) hχ = χ := by
    simpa only [hcomplex] using CoefficientCharacter.native_coefficient_character_lift D.pel hg
      (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ hχ
  rw [hlift] at hpurity
  exact hpurity

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectorPolynomialPurity
