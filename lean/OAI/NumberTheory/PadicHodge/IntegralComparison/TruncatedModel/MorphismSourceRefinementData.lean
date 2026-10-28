import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceCommonReferenceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceOldCoordinates

/-! # Morphism Source Refinement Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementData

noncomputable section

/-! The original source-refinement statement and its checked common-cover factor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

def statement (q : ℕ) : Prop :=
  (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f₁ hp₁ I₁ q).hom =
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u) q) ≫
      MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q

def commonStatement (q : ℕ) : Prop :=
  MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q =
    ModuleCech.CoefficientComposite.composite
      (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (WittVector p k)
      (MorphismCover.pairs p k n u)
      (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
      (MorphismCommonIsoCoordinates.source p k n u)
      (K := MorphismNewFrameCoordinates.Raw.sourceCoefficients p k n u f₁ hp₁)
      (L := MorphismNewFrameCoordinates.Raw.targetCoefficients p k n u f₁ I₁)
      (MorphismCommonIsoCoordinates.iso p k n u f₁ hp₁)
      (MorphismNewFrameCoordinates.Raw.coefficientMap p k n u f₁ hp₁ I₁)
      q (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)

theorem common_comparison (q : ℕ) : commonStatement p k n u f₁ hp₁ I₁ q :=
  SourceCommonReferenceCoordinates.MorphismReference.comparison p k n u f₁ hp₁ I₁ q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementData
