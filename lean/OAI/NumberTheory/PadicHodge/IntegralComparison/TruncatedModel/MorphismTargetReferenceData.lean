import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicComparisonTarget

/-! # Morphism Target Reference Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceData.ReferenceCoordinates

noncomputable section

/-! The original native target comparison proposition, checked separately
from the proof that joins its coordinate factors. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

attribute [local irreducible] HomologicalComplex.homology HomologicalComplex.homologyMap

def statement (i : ℕ) : Prop :=
    (MorphismIntrinsicBase.IntrinsicComparison.targetIso p k n f₂ hp₂ I₂ i).hom ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i) =
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u) i) ≫
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k).map
      (homologyMap (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u) i) ≫
      MorphismIntrinsicBase.IntrinsicComparison.commonComparison p k n u f₁ hp₁ I₁ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceData.ReferenceCoordinates
