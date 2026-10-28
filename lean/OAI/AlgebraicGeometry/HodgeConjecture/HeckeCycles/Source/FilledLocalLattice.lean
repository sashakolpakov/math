import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicRationalLattice

/-! # Filled Local Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocalLattice.CM

noncomputable section

/-! Integral preserved blocks give precisely the local lattice and
marked-difference conditions for the actual filled source operator. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicRationalLattice.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice.ParameterChoices
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL.CM.Intrinsic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem inverse (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (v : Fin s × Bool) :
    IntrinsicFilledPEL.CM.Intrinsic.blocks E D g⁻¹ v = (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g v)⁻¹ :=
  FilledBlocks.CM.block_inv E D.reference (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) g v

theorem integral_iff (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (∀ v, IntrinsicFilledPEL.CM.Intrinsic.blocks E D g v ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) ↔
      ∀ v : Fin s × Bool, v.1 ≠ D.reference.distinguished →
        Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) g.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
  FilledBlocks.CM.integral_iff E D.reference (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) g

variable (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hstandard : ∀ v, CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
  {J : Type*} [Fintype J] (b : Module.Basis J ℤ D.reference.lattice)

include hg hq hstandard in
theorem basis_iff (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (∀ j, CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g)
      (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) ↔
      ∀ v, IntrinsicFilledPEL.CM.Intrinsic.blocks E D g v ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
  (CMExtraction.SplitVectorEvaluation.TestTransport.span_basis_preserves_iff _ _ (CMExtraction.SplitVectorEvaluation.TestTransport.splitLatticeImage_span_basis E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice b)
    ((CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g)).restrictScalars (PadicInt q))).trans
      (CMExtraction.IntegralBlockLattice.TestTransport.localBlock_preserves_iff q _ (CMExtraction.Intrinsic.IntegralLattice.ParameterChoices.native_split_lattice_standard E D hg hq hstandard) (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g))

include hg hq hstandard in
theorem inverse_basis (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (h : ∀ j, CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g)
      (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) :
    ∀ j, CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g⁻¹)
      (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  apply (basis_iff E D hg hq hstandard b g⁻¹).mpr
  intro v
  have hv := (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem ((basis_iff E D hg hq hstandard b g).mp h v)
  exact (inverse E D g v).symm ▸ hv

omit [Fintype J] in
theorem difference_basis (N : ℕ) (hcop : q.Coprime N) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (h : ∀ j, CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g)
      (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) :
    ∀ j, (N : ℚ)⁻¹ • (CMExtraction.IntegralBlockLattice.TestTransport.localBlockLinear q (IntrinsicFilledPEL.CM.Intrinsic.blocks E D g)
      (CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) -
      CMExtraction.SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  intro j
  exact CMExtraction.PadicRationalLattice.TestTransport.padic_lattice_rational_division q N hcop _ _ _ (h j)
    (Submodule.subset_span ⟨(b j).val, (b j).property, rfl⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocalLattice.CM
