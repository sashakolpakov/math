import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicRationalLattice

/-! # Local Congruence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalCongruence.ParameterChoices

noncomputable section

/-! Integral native blocks give inverse preservation and the local
part of the original marked congruence at every good prime. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hstandard : ∀ v, SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
  {J : Type*} [Fintype J] (b : Module.Basis J ℤ D.reference.lattice)

include hg hq hstandard in
theorem nativeFilledBlocks_inverse_basis (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (h : ∀ j, IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)
      (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) :
    ∀ j, IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ⁻¹)
      (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  apply (LocalBlocks.ParameterChoices.nativeFilledBlocks_basis_iff E D hg hq hstandard b γ⁻¹).mpr
  intro v
  have hv := (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem
    ((LocalBlocks.ParameterChoices.nativeFilledBlocks_basis_iff E D hg hq hstandard b γ).mp h v)
  exact (LocalBlocks.ParameterChoices.nativeFilledBlock_inv E D γ v).symm ▸ hv

omit [Fintype J] in
theorem nativeFilledBlocks_difference_basis (N : ℕ) (hcop : q.Coprime N)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (h : ∀ j, IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)
      (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) :
    ∀ j, (N : ℚ)⁻¹ • (IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)
      (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) -
      SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice := by
  intro j
  exact PadicRationalLattice.TestTransport.padic_lattice_rational_division q N hcop _ _ _ (h j)
    (Submodule.subset_span ⟨(b j).val, (b j).property, rfl⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalCongruence.ParameterChoices
