import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTargetHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomologyCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetEdgeApplied

/-! # Morphism Intrinsic Target Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTargetRefinement.IntrinsicComparison

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

variable (i : ℕ)

abbrev targetEdge :=
  IntrinsicTargetEdgeApplied.MorphismIntrinsicStages.targetEdgeApplied p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i

abbrev targetSource :=
  targetEdge p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismSourceHomologyCoordinates.Raw.source_new p k n u f₁ I₁ i)

abbrev targetGlobal :=
  targetSource p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (GlobalTypedGeometricHomology.Morphism.comparison p k n v I₁ I₂ i)

abbrev targetFrame :=
  targetGlobal p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismGlobalTypedHomology.target_old p k n f₂ I₂ i)

abbrev targetCoefficient :=
  targetFrame p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i (WittVector p k)
    (SmoothWitt.DeRham.Comparison.coefficientFunctor p k)

abbrev targetIsos :=
  targetCoefficient p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i _ _ _
    (MorphismIntrinsicCoordinates.Intrinsic.targetIso p k n f₂ hp₂)
    (MorphismCoefficientCech.ordinaryTargetIso p k n u f₂ hp₂)
    (MorphismCoefficientCech.ordinarySourceIso p k n u f₁ hp₁)

abbrev targetMap :=
  targetIsos p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismIntrinsicCoordinates.Intrinsic.targetMap p k n u)

abbrev targetGeometricMap :=
  targetMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismOrdinaryCech.Ordinary.ordinaryMap p k n u)

abbrev targetRefinementSquare :=
  targetGeometricMap p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ i
    (MorphismIntrinsicCoordinates.Intrinsic.target p k n u f₂ hp₂).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicTargetRefinement.IntrinsicComparison
