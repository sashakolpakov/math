import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedMaps

/-! # Morphism Frame Typed Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedHomology

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

variable (q : ℕ)
def sourceOld : (MorphismFrameTypedMaps.Homology.sourceFrameOld p k n f₁ hp₁).homology q ⟶
    (MorphismFrameTypedMaps.Homology.sourceInjectiveOld p k n f₁ I₁).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.sourceOldMap p k n f₁ hp₁ I₁) q

def targetOld : (MorphismFrameTypedMaps.Homology.targetFrameOld p k n f₂ hp₂).homology q ⟶
    (MorphismFrameTypedMaps.Homology.targetInjectiveOld p k n f₂ I₂).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.targetOldMap p k n f₂ hp₂ I₂) q

def sourceNew : (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q ⟶
    (MorphismFrameTypedMaps.Homology.sourceInjectiveNew p k n u f₁ I₁).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.sourceNewMap p k n u f₁ hp₁ I₁) q

def targetNew : (MorphismFrameTypedMaps.Homology.targetFrameNew p k n u f₂ hp₂).homology q ⟶
    (MorphismFrameTypedMaps.Homology.targetInjectiveNew p k n u f₂ I₂).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.targetNewMap p k n u f₂ hp₂ I₂) q

def sourceFrameRefinement : (MorphismFrameTypedMaps.Homology.sourceFrameOld p k n f₁ hp₁).homology q ⟶
    (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.sourceFrameRefinementMap p k n u f₁ hp₁) q

def targetFrameRefinement : (MorphismFrameTypedMaps.Homology.targetFrameOld p k n f₂ hp₂).homology q ⟶
    (MorphismFrameTypedMaps.Homology.targetFrameNew p k n u f₂ hp₂).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.targetFrameRefinementMap p k n u f₂ hp₂) q

def sourceInjectiveRefinement : (MorphismFrameTypedMaps.Homology.sourceInjectiveOld p k n f₁ I₁).homology q ⟶
    (MorphismFrameTypedMaps.Homology.sourceInjectiveNew p k n u f₁ I₁).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.sourceInjectiveRefinementMap p k n u f₁ I₁) q

def targetInjectiveRefinement : (MorphismFrameTypedMaps.Homology.targetInjectiveOld p k n f₂ I₂).homology q ⟶
    (MorphismFrameTypedMaps.Homology.targetInjectiveNew p k n u f₂ I₂).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.targetInjectiveRefinementMap p k n u f₂ I₂) q

def geometric : (MorphismFrameTypedMaps.Homology.targetFrameNew p k n u f₂ hp₂).homology q ⟶
    (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology q :=
  HomologicalComplex.homologyMap (MorphismFrameTypedMaps.Homology.geometricMap p k n u v f₁ f₂ hp₁ hp₂ sq) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedHomology
