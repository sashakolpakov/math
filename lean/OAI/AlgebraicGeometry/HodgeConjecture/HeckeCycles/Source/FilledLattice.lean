import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticeSplit
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineCoordinateCompatibility

/-! # Filled Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLattice.CM

noncomputable section

/-! The actual filled source PEL operator has exactly the rational
localized-lattice and full q-adic lattice membership conditions. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineCoordinateCompatibility.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticeSplit.ParameterChoices
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL.CM.Intrinsic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hb : D.reference.b = B.b)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice)

include hg hq b in
theorem image_iff (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : Fin 3 → E) :
    (IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) ∈ D.reference.completedLattice ↔
      g.val.val *ᵥ x ∈ CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q ∧
        CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g) (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) ∈
          CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  have h := CMExtraction.Intrinsic.LatticeSplit.ParameterChoices.native_completed_lattice_split E D hg hq b
    ((IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) (g.val.val *ᵥ x)
    (FilledRationalCoordinates.CM.other E Q D.reference hb
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) (b.extendOfIsLattice ℚ).equivFun g x)
  exact h.trans (and_congr Iff.rfl (Iff.of_eq (congrArg
    (fun z => z ∈ CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice)
      (IntrinsicFilledPEL.CM.Intrinsic.rational_split E Q D hb hq g x))))

include hg hq b in
theorem difference_iff (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (r : ℚ) (x : Fin 3 → E) :
    r • ((IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) - AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) ∈
      D.reference.completedLattice ↔
      r • (g.val.val *ᵥ x - x) ∈ CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q ∧
        r • (CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g) (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) -
          CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) ∈
            CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  have ha : ∀ j (p : ℕ) [Fact p.Prime], p ≠ q →
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun
        (r • ((IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) - AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) j) =
          algebraMap ℚ (Padic p) ((b.extendOfIsLattice ℚ).equivFun (r • (g.val.val *ᵥ x - x)) j) := by
    intro j p _ hpq
    exact CMExtraction.AffineCoordinateCompatibility.TestTransport.coordinate_smul_sub_compatibility E (b.extendOfIsLattice ℚ).equivFun p j r _ _ _ _
      (FilledRationalCoordinates.CM.other E Q D.reference hb
        (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) (b.extendOfIsLattice ℚ).equivFun g x j p hpq)
      (CMExtraction.AffineCoordinateCompatibility.TestTransport.completedPadicCoordinate_rational E (b.extendOfIsLattice ℚ).equivFun p j x)
  have he : CMExtraction.SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D)
      (r • ((IntrinsicFilledPEL.CM.Intrinsic.hom E Q D hb g).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) - AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) =
        r • (CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g) (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) -
          CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) := by
    rw [map_smul, map_sub, IntrinsicFilledPEL.CM.Intrinsic.rational_split E Q D hb hq]
    exact congrArg (fun z => r • (CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g)
      (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) - z))
        (CMExtraction.SplitVectorEvaluation.TestTransport.finiteSplitEvaluation_rational E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x)
  exact (CMExtraction.Intrinsic.LatticeSplit.ParameterChoices.native_completed_lattice_split E D hg hq b _ _ ha).trans
    (and_congr Iff.rfl (Iff.of_eq (congrArg
      (fun z => z ∈ CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) he)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLattice.CM
