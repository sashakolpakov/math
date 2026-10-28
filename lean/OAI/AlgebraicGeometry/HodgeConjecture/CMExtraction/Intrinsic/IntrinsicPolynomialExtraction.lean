import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonRange
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricProjector
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Coefficient
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SameTestProjector
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntrinsicHecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ProjectorPolynomialPurity
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

/-! # Intrinsic Polynomial Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicPolynomialExtraction

noncomputable section

/-! Full projector comparison and Frobenius purity for a coefficient character
selected by the same nonzero projected theta test. The ordinary polynomial
is expressed on the exact integral model and Hecke realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates.Local
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters.Iwasawa OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors.Spectral
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

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Coefficient.Comparison

def NativeExtractionConclusion
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (i : Fin D.pel.componentCount)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (fstar : D.sphericalInputs) : Prop :=
    ∃ L : IntermediateField ℚ ℂ, NumberField L ∧ IsGalois ℚ L ∧
      ∃ (hEL : E ≤ L) (n : ℕ) (p : Fin n → L ⊗[ℚ] (D.pel.H1 →ₗ[ℚ] D.pel.H1))
        (initial : Fin n → ℚ),
      let V := D.pel.H1
      let H := Base.nativeH1 D hHodgeDecomposition hg
      let HB := Mem.canonicalH1 hHodgeDecomposition (D.componentVariety hg i).presentation
      let P := fun k => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L V V (p k)
      let C := fun k => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L V V (p k))
      let res := HeckeCycles.Coefficients.CM.coefficientRestriction E L (HeckeCycles.Coefficients.CM.all_embeddings_in_field E L hEL)
      GeometricProjector.Intrinsic.GeometricProjectorIdentification D.pel hg H L n p ∧
      (∃ k, P k (ThetaClass.nativeThetaClass D hg Θ fstar) ≠ 0) ∧
      (∀ k, (P k).comp (P k) = P k) ∧
      (∀ k, P k ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) ∧
      (∀ k, ∃ f, P k (ThetaClass.nativeThetaClass D hg Θ f) ≠ 0) ∧
      (∀ f, ∑ k, P k (ThetaClass.nativeThetaClass D hg Θ f) = ThetaClass.nativeThetaClass D hg Θ f) ∧
      (∀ k, initial k = -3 / 2) ∧
      (∀ k σ,
        (v.val (res σ) = true → Definitions.CM.conjugateSpace L (C k) σ ≤ H.holomorphic) ∧
        (v.val (res σ) = false → Definitions.CM.conjugateSpace L (C k) σ ≤ H.antiholomorphic)) ∧
      (∀ k (x : L ⊗[ℚ] V), x ∈ C k →
        ∃ f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V,
          f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H ∧
          ∀ τ : Gal(E/ℚ), f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) =
            if τ = 1 then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion L V x else 0) ∧
      (∀ k, LinearMap.range (P k) ≤ Definitions.CM.cmIdSpan E v H) ∧
      (∀ f, (Forms.componentRestriction D hg i).baseChange ℂ (ThetaClass.nativeThetaClass D hg Θ f) ∈
        Definitions.CM.cmIdSpan E v HB)

theorem native_polynomial_extraction
    (hHodgeDecomposition : Mem.HodgeDecompositionInput)
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (fstar : D.sphericalInputs) (hstar : ThetaClass.nativeThetaClass D hg Θ fstar ≠ 0) :
    NativeExtractionConclusion E D hg v hHodgeDecomposition i Θ fstar := by
  let H := Base.nativeH1 D hHodgeDecomposition hg
  let : FiniteDimensional ℚ D.pel.H1 := Base.native_betti_finite D hg
  let HR := NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull j
  let proj := ComparisonFiltration.nativeComparisonProjective D hg hq j
  have hHR := NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization_betti D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull j
  have hA := RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection_realizes D.pel hg hq hIsogenyQuotient (TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) hfull
  obtain ⟨L, hL, hGal, hEL, hLalg, m, p, χ, hid, hr, hh, hPc, hocc, hsum, hχ, hconj⟩ :=
    CommutingComparisonProjectors.Spectral.construct_commuting_comparison_projectors E H A.cohomologyAction
      (IntrinsicHecke.Intrinsic.native_hecke_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg hq hIsogenyQuotient A hA)
      (ThetaClass.nativeThetaClass D hg Θ) j.complexClosure
  let := hL
  let := hGal
  let P := fun k => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L D.pel.H1 D.pel.H1 (p k)
  have hpurity : ∀ k, NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j) j.fieldInClosure j.complexClosure HR proj
      (χ k) (fun τ => 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (ParameterChoices.restriction E ιE τ)) : ℚ) * (-3 / 2) / 3) := by
    intro k
    obtain ⟨f, hf⟩ := hocc k
    apply ProjectorPolynomialPurity.native_projector_polynomial_purity E D hg hμ v hv e he hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure
      ιE u i cover Θ hΘ huniq hq hIsogenyQuotient A coeff hfull eH heH hBetti c hp haway hElementaryDivisors
      (χ k) (P k) (hPc k) _ f hf hu side hside j hcomplex hopposite hpoly hGeometricComparison proj ℓ hℓq
    simpa only [hcomplex] using (hχ k).le
  refine ⟨L, hL, hGal, hEL, m, p, (fun _ => -3 / 2),
    ⟨hq, hIsogenyQuotient, A, coeff, hfull, j.complexClosure, hLalg, χ, hr, hPc, hχ, hconj⟩,
    SameTestProjector.same_test_projector_occurs P _ hstar (hsum fstar), hid, hh, hocc, hsum, ?_⟩
  apply Coefficient.Comparison.extraction_from_character_purity E L hEL hLalg v hv ιE
    (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D.pel hg hq j) j.fieldInClosure j.complexClosure _ HR proj D.pel.H1 H
    (ComparisonFiltration.nativeComparisonEquiv D hg hq j) (ComparisonFiltration.native_comparison_filtration D hg hq j hHodgeDecomposition)
    (Fin m) D.sphericalInputs (ThetaClass.nativeThetaClass D hg Θ) p χ (fun _ => -3 / 2)
    (fun _ => Or.inl rfl) hpurity hid hh (ThetaClass.nativeThetaClass_holomorphic D hHodgeDecomposition hg Θ)
    hocc hsum _ ((D.componentVariety hg i).rationalCohomology 1)
    (Mem.canonicalH1 hHodgeDecomposition (D.componentVariety hg i).presentation)
    (Forms.componentRestriction D hg i) (Base.native_componentRestriction_isHodgeMap D hHodgeDecomposition hg i)
  · intro x
    rw [hcomplex]
    exact RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding_spec ιE E.val.toRingHom x
  · intro k σ
    obtain ⟨τ, hτ, hH, hspace⟩ := hconj k σ
    exact ⟨τ, hτ, hH, ComparisonRange.native_comparison_range D hg hq j A hElementaryDivisors HR hHR _ _ hspace⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicPolynomialExtraction
