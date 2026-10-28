import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceEndpointsCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceExactOldCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicSourceCommonCoordinates

/-! # Morphism Source Refinement Equality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementEquality

noncomputable section

/-! The original source-refinement equality, closing the native comparison
with its checked endpoint coordinates. -/
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

abbrev endpoints (q : ℕ) :=
  IntrinsicSourceEndpointsCoordinates.MorphismIntrinsic.comparison p k n u f₁ hp₁ I₁ q
    (MorphismIntrinsicBase.IntrinsicComparison.sourceIso p k n f₁ hp₁ I₁ q).hom
    ((SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.sourceMap p k n u) q) ≫
      MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ q)

abbrev withLeft (q : ℕ) :=
  endpoints p k n u f₁ hp₁ I₁ q
    (SourceExactOldCoordinates.MorphismIntrinsic.comparison p k n f₁ hp₁ I₁ q)

abbrev withRight (q : ℕ) :=
  withLeft p k n u f₁ hp₁ I₁ q
    (IntrinsicSourceCommonCoordinates.MorphismIntrinsicRight.comparison p k n u f₁ hp₁ I₁ q)

theorem comparison (q : ℕ) :
    MorphismSourceRefinementData.statement p k n u f₁ hp₁ I₁ q := by
  exact withRight p k n u f₁ hp₁ I₁ q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementEquality
