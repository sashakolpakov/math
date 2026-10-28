import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LatticeSplit
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ResidualCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AffineCoordinateCompatibility
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitVectorEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBlockLattice

/-! # Filled Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledLattice.ParameterChoices

noncomputable section

/-! Images and marked differences under the actual filled native PEL
operator, in the original localized and split lattices. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)

include hq

theorem nativeFilledPEL_split_evaluate (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (Y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) :
    SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val Y) =
      IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ) (SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) Y) := by
  funext v
  exact FilledPEL.ParameterChoices.nativeFilledPEL_evaluate E D hg hq γ v Y

theorem nativeFilledPEL_rational_split (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) (x : Fin 3 → E) :
    SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D)
      ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) =
        IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ) (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) :=
  (nativeFilledPEL_split_evaluate E D hg hq γ _).trans
    (congrArg (IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ))
      (SplitVectorEvaluation.TestTransport.finiteSplitEvaluation_rational E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x))

variable {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ D.reference.lattice] (b : Module.Basis J ℤ D.reference.lattice)

include b

theorem nativeFilledPEL_lattice_image_iff (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) (x : Fin 3 → E) :
    (FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) ∈ D.reference.completedLattice ↔
      γ.val.val *ᵥ x ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q ∧
        IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ) (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) ∈
          SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  have h := LatticeSplit.ParameterChoices.native_completed_lattice_split E D hg hq b
    ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) (γ.val.val *ᵥ x)
    (ResidualCoordinates.ParameterChoices.nativeFilledPEL_other_coordinate E D hg (b.extendOfIsLattice ℚ).equivFun γ x)
  exact h.trans (and_congr Iff.rfl (Iff.of_eq (congrArg
    (fun z => z ∈ SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice)
      (nativeFilledPEL_rational_split E D hg hq γ x))))

theorem nativeFilledPEL_lattice_difference_iff (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (r : ℚ) (x : Fin 3 → E) :
    r • ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) - AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) ∈
      D.reference.completedLattice ↔
      r • (γ.val.val *ᵥ x - x) ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q ∧
        r • (IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)
          (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) -
          SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) ∈
            SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  have ha : ∀ j (p : ℕ) [Fact p.Prime], p ≠ q →
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (b.extendOfIsLattice ℚ).equivFun
        (r • ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) - AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) j) =
          algebraMap ℚ (Padic p) ((b.extendOfIsLattice ℚ).equivFun (r • (γ.val.val *ᵥ x - x)) j) := by
    intro j p hp hpq
    exact AffineCoordinateCompatibility.TestTransport.coordinate_smul_sub_compatibility E (b.extendOfIsLattice ℚ).equivFun p j r _ _ _ _
      (ResidualCoordinates.ParameterChoices.nativeFilledPEL_other_coordinate E D hg (b.extendOfIsLattice ℚ).equivFun γ x j p hpq)
      (AffineCoordinateCompatibility.TestTransport.completedPadicCoordinate_rational E (b.extendOfIsLattice ℚ).equivFun p j x)
  have he : SplitVectorEvaluation.TestTransport.finiteSplitEvaluation E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D)
      (r • ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) - AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) =
        r • (IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ) (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) -
          SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) := by
    rw [map_smul, map_sub, nativeFilledPEL_rational_split E D hg hq]
    exact congrArg (fun z => r • (IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)
      (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x) - z))
        (SplitVectorEvaluation.TestTransport.finiteSplitEvaluation_rational E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) x)
  exact (LatticeSplit.ParameterChoices.native_completed_lattice_split E D hg hq b _ _ ha).trans
    (and_congr Iff.rfl (Iff.of_eq (congrArg
      (fun z => z ∈ SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) he)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledLattice.ParameterChoices
