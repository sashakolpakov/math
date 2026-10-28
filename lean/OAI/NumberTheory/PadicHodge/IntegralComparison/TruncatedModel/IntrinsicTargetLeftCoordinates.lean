import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetIsoCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.IntrinsicCechComposite
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetReferenceFactors

/-! # Intrinsic Target Left Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetLeftCoordinates.MorphismIntrinsic

noncomputable section

/-! The original target comparison followed by crystalline pullback,
expressed through the native small-cover coefficient composite. -/
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
    (Witt.IntrinsicCechComposite.Intrinsic.composite p k
      (CechSliceResolution.opens p k n X₂)
      (MorphismRawEq.OldFrameCoordinates.coefficientMap p k n f₂ hp₂ I₂) i
      (IntrinsicTargetIsoCoordinates.MorphismIntrinsic.iso p k n f₂ hp₂ i).hom
      (GlobalEdge.InjectiveCech.homologyIso p k n X₂ Y₂ f₂ I₂ i).hom) ≫
      ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback v.left
        (MorphismData.Frames.ambient_over p k v) n i)

omit [IsSeparated Y₁.hom] in
theorem comparison (i : ℕ) : statement p k n v f₂ hp₂ I₂ i := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicTargetLeftCoordinates.MorphismIntrinsic
