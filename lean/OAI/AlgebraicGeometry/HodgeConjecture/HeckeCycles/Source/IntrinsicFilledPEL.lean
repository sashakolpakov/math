import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledRationalCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitVectorEvaluation

/-! # Intrinsic Filled PEL -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL.CM.Intrinsic

noncomputable section

/-! The actual PEL local characters label the filled source operator.
Its full q-adic evaluation and all other prime coordinates are retained. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitVectorEvaluation.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete.ParameterChoices

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hb : D.reference.b = B.b)

theorem labels_injective (hq : D.IsGoodCompletelySplitPrime) :
    Function.Injective (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) := by
  intro i j h
  apply CMExtraction.GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding_injective D hq
  ext x
  exact RingHom.congr_fun h x

def hom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* D.reference.FiniteSpecialUnitary :=
  FilledLocal.CM.PEL.hom E Q D.reference hb
    (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))

def blocks (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) : Fin s × Bool → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q :=
  FilledBlocks.CM.block E D.reference (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) g

variable [IsGalois ℚ E]

theorem evaluate (hq : D.IsGoodCompletelySplitPrime) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (v : Fin s × Bool) (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    (fun i => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) ((hom E Q D hb g).val x i)) =
      (blocks E D g v).val *ᵥ (fun i => CMExtraction.Finite.CoefficientPadic.TestTransport.finiteCoefficientPadic E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (x i)) :=
  FilledBlocks.CM.evaluate E Q D.reference hb (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D)
    (labels_injective E D hq) (CMExtraction.GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D hq) g v x

theorem split_evaluate (hq : D.IsGoodCompletelySplitPrime) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    CMExtraction.SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) ((hom E Q D hb g).val x) =
      CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (blocks E D g) (CMExtraction.SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) :=
  funext (fun v => evaluate E Q D hb hq g v x)

theorem rational_split (hq : D.IsGoodCompletelySplitPrime) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (x : Fin 3 → E) :
    CMExtraction.SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) ((hom E Q D hb g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) =
      CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (blocks E D g) (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) :=
  (split_evaluate E Q D hb hq g _).trans
    (congrArg (CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (blocks E D g))
      (CMExtraction.SplitVectorEvaluation.TestTransport.finiteSplitEvaluation_rational E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL.CM.Intrinsic
