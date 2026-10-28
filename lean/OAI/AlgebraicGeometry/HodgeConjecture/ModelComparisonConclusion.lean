import OAI.AlgebraicGeometry.HodgeConjecture.FixedPrincipalComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeSeed
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.UniformComparisonCanonical

/-! # Model Comparison Conclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ModelComparisonConclusion.CMExtractionIntrinsic

noncomputable section

section

/-! Extract CM classes on the retained integral model, using its actual
ordinary reduction and the normalized test fixed before the prime. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C
local notation "hg" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel_geometry E P hP hμ v hv W R M j₀ C

def RetainedFixedTestComparisonConclusion (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) : Prop :=
  let : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
  let D := CMExtraction.HeckeSeed.Intrinsic.retainedThetaSeed E P hP hμ v hv W R M j₀ C
  ∃ hq : D.pel.IsGoodCompletelySplitPrime,
  ∃ u : MpF,
    D.weil.finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q
      (CMExtraction.Intrinsic.FiniteCoordinates.nativeFiniteCoordinateMatrix E D hg hq v R.coordinates R.pairing) ∧
    ∃ hu : CMExtraction.Intrinsic.FiniteDilation.NativeFiniteCoordinateIdentity E D R.coordinates u,
      let c : (Fin s × Fin 3) ≃ Fin (s * 3) := finProdFinEquiv
      let := CMExtraction.Intrinsic.UnitaryAwayTopology.nativeUnitaryAwayTopology E D hg hμ v hv R.coordinates R.pairing c u hu
        (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D)
      let hlevel : 0 < D.pel.level := lt_of_lt_of_le (by decide : 0 < 3) M.level_ge_three
      let L := CMExtraction.Intrinsic.PELLevel.nativePELLevel E D hg hμ v hv R.coordinates R.pairing c u hu
        (CMExtraction.Intrinsic.UnitaryAwayDensity.nativeUnitaryActivePlace E D) hlevel
      let N := RepresentationTheory.Hecke.IntrinsicDatum.SphericalActionIntrinsic.nativeDatum E D hg hμ v hv R.coordinates R.pairing c u hu L
      ∃ hf : R.thetaTest.test ∈ N.sphericalInputs,
        IntrinsicGeometricThetaComparison.CMExtractionIntrinsic.NativeGeometricThetaComparisonConclusion E N hg v hHodgeDecomposition ιE ⟨R.thetaTest.test, hf⟩

def RetainedModelComparisonConclusion (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) : Prop :=
  RetainedFixedTestComparisonConclusion E P hP hμ v hv W R M j₀ C hHodgeDecomposition ιE ∧
  (let : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
   let D := CMExtraction.HeckeSeed.Intrinsic.retainedThetaSeed E P hP hμ v hv W R M j₀ C
   UniformComparisonCanonical.CMExtractionIntrinsic.UniformComparisonModelConclusion E D hg hμ ιE v hv)

end

/-! Extract CM classes on the retained integral model, using its actual
ordinary reduction and the normalized test fixed before the prime. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

attribute [local instance] CMExtraction.Intrinsic.Multiplicity.nativePlaceDecidableEq CMExtraction.Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : CMExtraction.Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : CMExtraction.PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : CMExtraction.Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C
local notation "hg" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel_geometry E P hP hμ v hv W R M j₀ C

theorem retained_seed_comparison
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hgood : CMExtraction.PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q)
    (hIsogenyQuotient : (HD).RealizesIsogenyQuotient)
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (side : Fin s → Bool)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
    (hcomplex : j.complexClosure = RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (hopposite : j.iota = CMExtraction.Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE HD)
    (hpoly : CMExtraction.Intrinsic.OrdinaryPolynomial.NativeOrdinaryPolynomial HD hg
      (CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel_good_prime E P hP hμ v hv W R M j₀ C hgood) hIsogenyQuotient side j)
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hGeometricTheta : RepresentationTheory.Hecke.SphericalAction.GeometricThetaInput) (hRadialDilation : RepresentationTheory.Hecke.SphericalAction.RadialDilationInput.{0, 0})
    (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition) (hPoissonAutomorphy : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0, 0, 0, 0})
    (hRationalStructure : RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (hTateComparison : HeckeCycles.TateComparison.CM.TateComparisonInput)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparison.FrobeniusSlope.GeometricComparisonInput) :
    RetainedModelComparisonConclusion E P hP hμ v hv W R M j₀ C hHodgeDecomposition ιE := by
  let : TopologicalSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) := ⊥
  let D := CMExtraction.HeckeSeed.Intrinsic.retainedThetaSeed E P hP hμ v hv W R M j₀ C
  have hqD := CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel_good_prime E P hP hμ v hv W R M j₀ C hgood
  have hc := CMExtraction.HeckeSeed.Intrinsic.retainedThetaSeed_finiteCoordinates E P hP hμ v hv W R M j₀ C hgood
  have hTateComparisonD : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput HD hg hqD hIsogenyQuotient :=
    CMExtraction.TateComparison.Intrinsic.native_full_c47_input hTateComparison s hs hdegree q HD hg hqD hIsogenyQuotient hConstruction hElementaryDivisors
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have htwo : 2 ≠ q := (lt_of_le_of_lt (le_max_left 2 _) hgood.test_large).ne
  obtain ⟨u, hproject, hu, hf, hout⟩ := FixedPrincipalComparison.CMExtractionIntrinsic.retained_principal_comparison hHodgeDecomposition hGeometricTheta hRadialDilation hLocalWeil hPoissonAutomorphy hRationalStructure
    E hs hdegree D hg hqD hIsogenyQuotient hTateComparisonD hc hμ ιE v hv R finProdFinEquiv
    (Nat.mul_pos hs (by decide)) (lt_of_lt_of_le (by decide : 0 < 3) M.level_ge_three)
    M.depth_dvd hgood.test_large hConstruction hHodgeComparison hElementaryDivisors side j hcomplex hopposite hpoly hGeometricComparison 2 htwo
  refine ⟨⟨hqD, u, hproject, hu, hf, hout⟩, ?_⟩
  exact ⟨hqD, hIsogenyQuotient, side, j, hcomplex, hopposite,
    UniformComparisonCanonical.CMExtractionIntrinsic.uniform_comparison_on_constructed_data E D hg hμ ιE v hv
      hs hdegree hqD hIsogenyQuotient hc side j hcomplex hopposite hpoly hGeometricComparison⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ModelComparisonConclusion.CMExtractionIntrinsic
