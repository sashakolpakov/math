import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicProjectorComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicPolynomialExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ComparisonRange
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
import OAI.RepresentationTheory.Hecke.IntrinsicDatum
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FiniteCoordinates

/-! # Intrinsic Geometric Theta Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicGeometricThetaComparison.CMExtractionIntrinsic

noncomputable section

section

/-! Full projector comparison and Frobenius purity for a coefficient character
selected by the same nonzero projected theta test. The ordinary polynomial
is expressed on the exact integral model and Hecke realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedParameters.Iwasawa OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CommutingComparisonProjectors.Spectral
open scoped Classical TensorProduct

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

def NativeGeometricThetaComparisonConclusion
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (fstar : D.sphericalInputs) : Prop :=
    ∃ (i : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (component : X.toOver ≅ D.componentComplex i) (cover : D.domain → X.analyticSpace)
      (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA),
      X.complexDimension = 2 ∧ D.IsPeriodUniformization X cover ∧
      D.IsCanonicalThetaLift hg i (D.totalPeriodMap i X component cover) Θ ∧
      CMExtraction.Intrinsic.ThetaClass.nativeThetaClass D hg Θ fstar ≠ 0 ∧ CMExtraction.Intrinsic.IntrinsicPolynomialExtraction.NativeExtractionConclusion E D hg v hHodgeDecomposition i Θ fstar ∧
      ∃ (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
        (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q),
        j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE ∧
        j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel ∧
        ∃ (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
          (coeff : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Local.IntegralType s →₀ ℕ)
          (hfull : AbelianScheme.CentralAction.Interface.Construction.Conclusion D.pel hg hq hIsogenyQuotient (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)),
          A.IsRealization D.pel hg hq hIsogenyQuotient ∧
          Nonempty (NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D.pel hg hq j) ∧
          ∀ (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1)),
          (∀ h, Commute P ((A.cohomologyAction h).baseChange ℂ)) →
          LinearMap.range P ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ)
            (fun h => RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (χ h)) →
          ∀ f : D.sphericalInputs, P (CMExtraction.Intrinsic.ThetaClass.nativeThetaClass D hg Θ f) ≠ 0 →
          ∀ (proj : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D.pel hg hq j)
            (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q →
          ∃ (rCM : Eˣ) (M : ℕ) (ω ζ : ℂ), 0 < M ∧
            ∃ hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D.pel (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) h).genEigenspace
              (CMExtraction.Intrinsic.CoefficientCharacter.nativeCoefficientCharacter (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ h) ⊤) ≠ ⊥,
            ComparisonConclusion.CMExtractionIntrinsic.FullComparisonConclusion E D.pel hg hq hIsogenyQuotient (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff)
              hfull ιE v rCM M ω ζ
              (CMExtraction.Intrinsic.CoefficientCharacter.nativeCoefficientCharacter (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE) χ) hχ side j proj ℓ

theorem native_c48_comparison
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (u : MpF)
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (haway : ∀ g ∈ D.awayLevel, ∀ p t : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.weil.finite.project (u * D.splitting (1, g) * u⁻¹)).val.mulVec
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t))
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (hu : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (CMExtraction.Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v e he))
    (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient) (hGeometricTheta : CMExtraction.GeometricTheta.Intrinsic.GeometricThetaOutput D hg hq hIsogenyQuotient)
    (hframe : (CMExtraction.Intrinsic.CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).thetaUniversal = D.thetaUniversal)
    (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial D.pel hg hq hIsogenyQuotient side j)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (fstar : D.sphericalInputs) (z : D.domain) (dz : Fin 2 → ℂ)
    (hvalue : D.thetaUniversal fstar.val z.val dz ≠ 0) :
    NativeGeometricThetaComparisonConclusion E D hg v hHodgeDecomposition ιE fstar := by
  obtain ⟨A, hA, eH, _, _, hraw, i, X, component, cover, hdim, hcover, _, _,
    rho, hrho, Θ, hΘ, huniq, hcov⟩ := hGeometricTheta
  have hstar := CMExtraction.Intrinsic.NonzeroClass.nativeThetaClass_ne_zero_of_period_value D hg Θ i X component cover hcover hΘ
    fstar z dz hvalue
  refine ⟨i, X, component, cover, Θ, hdim, hcover, hΘ, hstar, ?_⟩
  obtain ⟨coeff, hfull⟩ := CMExtraction.TateComparisonCompletion.Intrinsic.native_action_full_conclusion D.pel hg hq hIsogenyQuotient hTateComparison A hA
  have heH := CMExtraction.CanonicalActiveEquiv.Local.activeHeckeEquiv_eq_of_raw_matching q D.pel.reference.distinguished A.basis hA.basis eH hraw
  have hBetti := CMExtraction.ComparisonIntrinsicClass.Intrinsic.nativeThetaClass_hecke D hg (CMExtraction.Intrinsic.Albanese.nativeAlbaneseProjectiveOfGeometry D hg)
    hq hIsogenyQuotient A hA rho hrho eH Θ hcov
  have hside : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D.pel (CMExtraction.TateComparisonCompletion.Intrinsic.fullNativeAction D.pel A coeff) D.pel.reference.distinguished side :=
    CMExtraction.Intrinsic.CentralFinite.native_central_actions_finite_order D.pel hg hq hIsogenyQuotient hdegree hTateComparison A hA D.pel.reference.distinguished side
  have hΘ' : (CMExtraction.Intrinsic.CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg i
      (D.totalPeriodMap i X component cover) Θ := by
    refine ⟨hΘ.1, ?_, hΘ.2.2⟩
    intro φ x p hp
    rw [hframe]
    exact hΘ.2.1 φ x p hp
  have huniq' : ∀ Ψ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA,
      (CMExtraction.Intrinsic.CotangentCovariance.withNativeCotangentTheta E D hg hμ v hv e he).IsCanonicalThetaLift hg i
        (D.totalPeriodMap i X component cover) Ψ → Ψ = Θ := by
    intro Ψ hΨ
    apply huniq Ψ
    refine ⟨hΨ.1, ?_, hΨ.2.2⟩
    intro φ x p hp
    rw [← hframe]
    exact hΨ.2.1 φ x p hp
  constructor
  · exact CMExtraction.Intrinsic.IntrinsicPolynomialExtraction.native_polynomial_extraction E D hg hμ v hv e he hHodgeDecomposition hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure
      ιE u i (D.totalPeriodMap i X component cover) Θ hΘ' huniq' hq hIsogenyQuotient A coeff hfull
      eH heH hBetti c hp haway hElementaryDivisors hu side hside j hcomplex hopposite (hpoly _ hfull)
      hGeometricComparison ℓ hℓq hConstruction hHodgeComparison fstar hstar
  · refine ⟨hq, hIsogenyQuotient, side, j, hcomplex, hopposite, A, coeff, hfull, hA,
      ⟨CMExtraction.Intrinsic.ComparisonFiltration.nativeComparisonProjective D hg hq j⟩, ?_⟩
    intro χ P hP hspace f hne proj ℓ' _ hℓ'q
    exact IntrinsicProjectorComparison.CMExtractionIntrinsic.native_projector_comparison_and_purity E D hg hμ v hv e he hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure
      ιE u i (D.totalPeriodMap i X component cover) Θ hΘ' huniq' hq hIsogenyQuotient A coeff hfull
      eH heH hBetti c hp haway hElementaryDivisors χ P hP hspace f hne hu side hside j hcomplex hopposite
      (hpoly _ hfull) hGeometricComparison proj ℓ' hℓ'q

end

/-! Literal identities for the constructed native datum, kept separate
so subsequent geometric assembly reuses their checked proofs. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hμ : D.pel.reference.μ = E.val.toRingHom)
  (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (D.pel.reference.imaginaryScalar * CMExtraction.Intrinsic.Multiplicity.nativeTensorPairing E D.pel.reference v x y))
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)
  (hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D e u)

variable [TopologicalSpace (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu)]
  (L : OpenSubgroup (RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.NativeAway E D hg hμ v hv e he c u hu))

local notation "N" => OAI.RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv e he c u hu L

/-- Specialize the checked extraction theorem to the constructed datum. -/
theorem nativeGeometricThetaComparisonAtDatum : type_of% (native_c48_comparison E N hg hμ v hv e he) :=
  native_c48_comparison E N hg hμ v hv e he

end

end OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicGeometricThetaComparison.CMExtractionIntrinsic
