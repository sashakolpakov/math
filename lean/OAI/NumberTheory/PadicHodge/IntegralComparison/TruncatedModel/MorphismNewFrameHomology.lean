import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicComparisonSource

/-! # Morphism New Frame Homology -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameHomology.SourceComparisonMaps

/-! The cochain maps and separate homology factors of the original
source comparison, before composing their native coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

theorem old_map :
    FrameCech.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁ =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.map.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (CechSliceResolution.opens p k n X₁)
        (FrameInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁) := rfl

theorem new_map :
    MorphismFrameTypedMaps.Homology.sourceNewMap p k n u f₁ hp₁ I₁ =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
        (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁) := rfl

theorem old_homology (q : ℕ) :
    (GlobalFrame.Comparison.homologyIso p k n X₁ Y₁ f₁ hp₁ I₁ q).hom =
      homologyMap (FrameCech.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁) q ≫
        (GlobalEdge.InjectiveCech.homologyIso p k n X₁ Y₁ f₁ I₁ q).hom := rfl

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem old_comparison (q : ℕ) :
    (GlobalEdge.InjectiveCech.homologyIso p k n X₁ Y₁ f₁ I₁ q).hom =
      MorphismGlobalTypedHomology.sourceOldComparison p k n f₁ I₁ q := rfl

theorem new_homology (q : ℕ) :
    MorphismIntrinsicBase.IntrinsicComparison.frameCommonComparison p k n u f₁ hp₁ I₁ q =
      homologyMap (MorphismFrameTypedMaps.Homology.sourceNewMap p k n u f₁ hp₁ I₁) q ≫
        MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameHomology.SourceComparisonMaps

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameHomology.Raw

/-! The original common-source frame factorization, with its equality
carrier determined by the explicit homology composite. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

theorem reverse (q : ℕ) :
    homologyMap
        (MorphismFrameTypedMaps.Homology.sourceNewMap p k n u f₁ hp₁ I₁) q ≫
      MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q =
    MorphismIntrinsicBase.IntrinsicComparison.frameCommonComparison p k n u f₁ hp₁ I₁ q := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismNewFrameHomology.Raw

end

end OAI
