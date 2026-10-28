import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CommonReferenceIsoCoordinates

/-! # Source Common Reference Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceCommonReferenceCoordinates.MorphismReference

noncomputable section

/-! The original common-cover composite, including its coefficient
isomorphism and its explicitly typed homology map. -/
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

private abbrev withFirst (q : ℕ) := ModuleCech.CoefficientComposite.comparison p k
  (MorphismCover.pairs p k n u)
  (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)
  (MorphismCommonIsoCoordinates.source p k n u)
  (K := MorphismNewFrameCoordinates.Raw.sourceCoefficients p k n u f₁ hp₁)
  (L := MorphismNewFrameCoordinates.Raw.targetCoefficients p k n u f₁ I₁)
  (MorphismCommonIsoCoordinates.iso p k n u f₁ hp₁)
  (MorphismNewFrameCoordinates.Raw.coefficientMap p k n u f₁ hp₁ I₁) q
  (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
  (MorphismNewFrameData.RawCoordinates.named_first p k n u f₁ hp₁ I₁ q)

private abbrev withIso (q : ℕ) :=
  withFirst p k n u f₁ hp₁ I₁ q
    (MorphismIntrinsicHomology.Intrinsic.commonSourceIso p k n u f₁ hp₁ q).hom

abbrev comparison (q : ℕ) :=
  withIso p k n u f₁ hp₁ I₁ q
    (CommonReferenceIsoCoordinates.MorphismReference.comparison p k n u f₁ hp₁ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceCommonReferenceCoordinates.MorphismReference
