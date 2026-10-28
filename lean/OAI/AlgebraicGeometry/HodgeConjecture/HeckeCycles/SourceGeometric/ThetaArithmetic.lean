import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaOrdinaryParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArithmeticFromValues
import Lean.LibrarySuggestions.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum

/-! # Theta Arithmetic -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaArithmetic.CM

/-! The ordinary character values prove the arithmetic proposition on
an actual source witness before introducing its comparison realization. -/

open scoped Classical TensorProduct _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  (hμ : D.reference.μ = E.val.toRingHom)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)

local notation "T" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM.data E L D hb b hN

include hμ in
theorem arithmetic
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, 0, 0, 0})
    (hTateComparison : TateComparison.CM.TateComparisonInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness T hg hq hIsogenyQuotient)
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (hd : ∀ τ, d τ = v.val τ⁻¹)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (hχ : D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (fullSide : Fin places.count → Bool)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    Source.ArithmeticFromValues.CM.HeckeExtraction.Arithmetic E T hg hq hIsogenyQuotient W j fullSide v :=
  Source.ArithmeticFromValues.CM.arithmetic E T hg hq hIsogenyQuotient W j fullSide v
    (ThetaOrdinaryParameters.CM.Ordinary.parameters E L D hb hμ b hN
      hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hTateComparison hConstruction hg hq hIsogenyQuotient W v hv hd
      j hχ fullSide hElementaryDivisors)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaArithmetic.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaArithmetic.CM.Extraction

/-! Extract all actual GeometricTheta source theta classes from the full named
auxiliary and Hecke prerequisites and the comparison constructed on the
same original Albanese. The source arithmetic premise is proved here. -/

open scoped Classical TensorProduct _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  (hμ : D.reference.μ = E.val.toRingHom)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)

local notation "T" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM.data E L D hb b hN

include hμ in
abbrev extraction
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, 0, 0, 0})
    (hTateComparison : TateComparison.CM.TateComparisonInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput) (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness T hg hq hIsogenyQuotient)
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (hd : ∀ τ, d τ = v.val τ⁻¹)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (hχ : D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (fullSide : Fin places.count → Bool)
    (hcop : Nat.Coprime q D.denominator) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    letI : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) :=
      TateComparisonAction.CM.commutativeHeckeRing places.count q hElementaryDivisors
    let AM := AlbaneseModel.CM.comparisonModel D hg j hcop
    ∀ (R : AM.HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q))
    (_hbetti : AM.bettiHecke D.complexEmbedding R = (fun h => W.action.cohomologyAction h))
    (_hc : Constructed.Comparison.CM.Conclusion AM j.fieldInClosure j.complexClosure j.iota R
      (fun i => W.action.basis (Neighbor.Types.CM.integralType D.reference.distinguished fullSide i).val))
    (_hCMExtraction : MatchedLevelExtraction.CM.Construction.CMExtractionInput.{0, 0, 0, 0}),
    ∀ φ : (T).sphericalInputs,
      Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W φ ∈
        MatchedLevelExtraction.CM.Construction.lineImageSpan E v (CMExtraction.Intrinsic.Base.nativeH1 T hHodgeDecomposition hg) := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) :=
    TateComparisonAction.CM.commutativeHeckeRing places.count q hElementaryDivisors
  intro AM R hbetti hc hCMExtraction
  exact Source.ArithmeticFromValues.CM.HeckeExtraction.extraction E T hg hq hIsogenyQuotient W j hcop hElementaryDivisors fullSide v hv
    R hbetti hHodgeDecomposition hConstruction hHodgeComparison hμ hc
    (arithmetic E L D hb hμ b hN
      hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hTateComparison hConstruction hg hq hIsogenyQuotient W v hv hd
      j hχ fullSide hElementaryDivisors) hCMExtraction

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaArithmetic.CM.Extraction

end

end OAI
