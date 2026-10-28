import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicLevelComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.DatumIdentities
import OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicGeometricThetaComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PrincipalGeometricTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicPolynomialExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.BettiNonzero
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalTest

/-! # Fixed Principal Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.FixedPrincipalComparison.CMExtractionIntrinsic

noncomputable section

section

/-! The full fixed-coordinate projector comparison and Frobenius-purity
output is inhabited by the normalized test chosen before the auxiliary prime,
on the original principal level. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.CategoryTheory

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

theorem fixed_principal_comparison
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput) (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hc : D.HasFiniteCoordinates) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E D.pel.reference hg.reference_admissible hμ v hv D.weil)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n)
    (hlevel : 0 < D.pel.level)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial D.pel hg hq hIsogenyQuotient side j)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (u : MpF)
    (hproject : D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (CMExtraction.Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v R.coordinates R.pairing))
    (hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D R.coordinates u) :
    let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
      (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
    let L := CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
      (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
    let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv R.coordinates R.pairing c u hu L
    ∀ hf : R.thetaTest.test ∈ N.sphericalInputs,
      IntrinsicGeometricThetaComparison.CMExtractionIntrinsic.NativeGeometricThetaComparisonConclusion E N hg v hHodgeDecomposition ιE ⟨R.thetaTest.test, hf⟩ := by
  dsimp only
  let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
    (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let L := CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
    (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
  let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv R.coordinates R.pairing c u hu L
  intro hf
  have hout := CMExtraction.Intrinsic.PrincipalGeometricTheta.native_principal_c48_output hGeometricTheta E hs hdegree D hg hq hIsogenyQuotient hTateComparison hc hμ
    v hv c R.coordinates R.pairing u hu hlevel
  let z := CMExtraction.Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E D.pel.reference hg.reference_admissible
  have hz : z.val ∈ N.domain := by
    change z.val ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (D.pel.reference.μ D.pel.reference.b) : Set (Fin 2 → ℂ))
    rw [← CMExtraction.Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E D.pel.reference]
    exact z.property
  have hvalue : N.thetaUniversal R.thetaTest.test z.val (Pi.single 0 1) ≠ 0 := by
    have h : N.thetaUniversal R.thetaTest.test z.val (Pi.single 0 1) = 1 := R.thetaTest.value
    rw [h]
    exact one_ne_zero
  exact IntrinsicLevelComparison.CMExtractionIntrinsic.native_level_comparison hHodgeDecomposition hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure E hdegree D hg hq hIsogenyQuotient hTateComparison hμ
    ιE v hv R.coordinates R.pairing c hConstruction hHodgeComparison hElementaryDivisors side j hcomplex hopposite hpoly hGeometricComparison ℓ hℓq
    u hproject hu L hout ⟨R.thetaTest.test, hf⟩ ⟨z.val, hz⟩ (Pi.single 0 1) hvalue

end

/-! The full fixed-coordinate projector comparison and Frobenius-purity
output is inhabited by the normalized test chosen before the auxiliary prime,
on the original principal level. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.CategoryTheory

open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CanonicalActiveEquiv.Local

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

theorem retained_principal_comparison
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput) (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hc : D.HasFiniteCoordinates) (hμ : D.pel.reference.μ = E.val.toRingHom)
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
    (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E D.pel.reference hg.reference_admissible hμ v hv D.weil)
    {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (hn : 0 < n)
    (hlevel : 0 < D.pel.level) (hdepth : R.depth ∣ D.pel.level)
    (hlarge : max 2 (max R.thetaTest.level
      (CMExtraction.Intrinsic.FiniteCoordinates.nativeCoordinateBound E D.pel.reference hg.reference_admissible v R.coordinates R.pairing)) < q)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D.pel)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial D.pel hg hq hIsogenyQuotient side j)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ u : MpF,
      D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
        (CMExtraction.Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v R.coordinates R.pairing) ∧
      ∃ hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D R.coordinates u,
        let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
          (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
        let L := CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
          (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
        let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv R.coordinates R.pairing c u hu L
        ∃ hf : R.thetaTest.test ∈ N.sphericalInputs,
          IntrinsicGeometricThetaComparison.CMExtractionIntrinsic.NativeGeometricThetaComparisonConclusion E N hg v hHodgeDecomposition ιE ⟨R.thetaTest.test, hf⟩ := by
  obtain ⟨u, hproject, hu, hf, _, _⟩ :=
    CMExtraction.CanonicalTest.Intrinsic.native_retained_canonical_test E D hg hq hμ v hv R hLocalWeil c hn hlevel hdepth hlarge
  refine ⟨u, hproject, hu, ?_⟩
  dsimp only
  let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
    (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
  let L := CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
    (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
  let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv R.coordinates R.pairing c u hu L
  refine ⟨hf, ?_⟩
  exact fixed_principal_comparison hHodgeDecomposition hGeometricTheta hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure E hs hdegree D
    hg hq hIsogenyQuotient hTateComparison hc hμ ιE v hv R c hlevel hConstruction hHodgeComparison hElementaryDivisors side j hcomplex hopposite
    hpoly hGeometricComparison ℓ hℓq u hproject hu hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.FixedPrincipalComparison.CMExtractionIntrinsic
