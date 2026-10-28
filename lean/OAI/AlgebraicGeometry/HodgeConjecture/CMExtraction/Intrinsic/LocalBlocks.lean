import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralBlockLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitVectorEvaluation

/-! # Local Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalBlocks

noncomputable section

/-! The original lattice basis detects integrality of every retained
native local block. Inversion retains the same integral blocks. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

namespace TestTransport

theorem conditional_hom_inv {G H : Type*} [Group G] [Group H]
    (p : Prop) [Decidable p] (f : G →* H) (g : G) :
    (if p then 1 else f g⁻¹) = (if p then 1 else f g)⁻¹ := by
  by_cases hp : p <;> simp only [hp, ite_true, ite_false, map_inv, inv_one]

end TestTransport

namespace ParameterChoices

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

omit [IsGalois ℚ E] in
theorem nativeFilledBlock_inv (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) (v : Fin s × Bool) :
    FilledPEL.ParameterChoices.nativeFilledBlock E D γ⁻¹ v = (FilledPEL.ParameterChoices.nativeFilledBlock E D γ v)⁻¹ :=
  TestTransport.conditional_hom_inv (v.1 = D.reference.distinguished)
    ((Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v)).comp
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (IsCMField.complexConj E).toRingHom D.reference.b).subtype) γ

omit [IsGalois ℚ E] in
theorem nativeFilledBlocks_integral_iff (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) :
    (∀ v, FilledPEL.ParameterChoices.nativeFilledBlock E D γ v ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) ↔
      ∀ v : Fin s × Bool, v.1 ≠ D.reference.distinguished →
        Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) γ.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
  IntegralBlockLattice.TestTransport.identity_blocks_integral_iff (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (fun v : Fin s × Bool => v.1 = D.reference.distinguished)
    (fun v => Matrix.SpecialLinearGroup.map (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) γ.val)

variable (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hstandard : ∀ v, SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
  {J : Type*} [Fintype J] (b : Module.Basis J ℤ D.reference.lattice)

include hg hq hstandard in
omit [IsGalois ℚ E] in
theorem nativeFilledBlocks_basis_iff (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b) :
    (∀ j, IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)
      (SplitVectorEvaluation.TestTransport.rationalSplitEmbedding E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) (b j).val) ∈
        SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice) ↔
      ∀ v, FilledPEL.ParameterChoices.nativeFilledBlock E D γ v ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q :=
  (SplitVectorEvaluation.TestTransport.span_basis_preserves_iff _ _ (SplitVectorEvaluation.TestTransport.splitLatticeImage_span_basis E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice b)
    ((IntegralBlockLattice.TestTransport.localBlockLinear q (FilledPEL.ParameterChoices.nativeFilledBlock E D γ)).restrictScalars (PadicInt q))).trans
      (IntegralBlockLattice.TestTransport.localBlock_preserves_iff q _ (IntegralLattice.ParameterChoices.native_split_lattice_standard E D hg hq hstandard)
        (FilledPEL.ParameterChoices.nativeFilledBlock E D γ))

end ParameterChoices

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.LocalBlocks
