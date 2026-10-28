import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameGlobalSourceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedHomology

/-! # Morphism Intrinsic Base -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicBase.IntrinsicComparison

noncomputable section

/-! The native ordinary de Rham comparison factors through the same
common affine cover as the original bounded crystalline pullback. -/

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

omit [IsSeparated Y₁.hom] in
theorem source_refinement :
    MorphismCoefficientCech.sourceRefinement p k n u f₁ hp₁ =
      MorphismFrameRefinementCoordinates.Comparison.sourceFrameRefinement p k n u f₁ hp₁ := rfl

omit [IsSeparated Y₂.hom] in
theorem target_refinement :
    MorphismCoefficientCech.targetRefinement p k n u f₂ hp₂ =
      MorphismFrameRefinementCoordinates.Comparison.targetFrameRefinement p k n u f₂ hp₂ := rfl

abbrev geometric_map :=
  Eq.refl (MorphismCoefficientCech.geometricMap p k n u v f₁ f₂ hp₁ hp₂ sq)

variable (i : ℕ)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k
local notation "c" => HomologicalComplex.homologyMap
  (MorphismFrameCechHomology.sourceComparison p k n u f₁ hp₁ I₁) i ≫
    Iso.hom (MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ i)
local notation "g" => ModuleCat.ofHom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left
  (MorphismData.Frames.ambient_over p k v) n i)

def frameCommonComparison :
    (MorphismFrameTypedMaps.Homology.sourceFrameNew p k n u f₁ hp₁).homology i ⟶
      ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
          (J := Ideal.span {(p : WittVector p k)})
          (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
          (Witt.Crystalline.wittStructureMap p k Y₁) n i) :=
  MorphismFrameTypedHomology.sourceNew p k n u f₁ hp₁ I₁ i ≫
    MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ i

def commonComparison :=
  (MorphismIntrinsicHomology.Intrinsic.commonSourceIso p k n u f₁ hp₁ i).hom ≫
    frameCommonComparison p k n u f₁ hp₁ I₁ i

def sourceIso := MorphismIntrinsicHomology.Intrinsic.sourceIso p k n f₁ hp₁ i ≪≫
  GlobalFrame.Comparison.homologyIso p k n X₁ Y₁ f₁ hp₁ I₁ i

def targetIso := MorphismIntrinsicHomology.Intrinsic.targetIso p k n f₂ hp₂ i ≪≫
  GlobalFrame.Comparison.homologyIso p k n X₂ Y₂ f₂ hp₂ I₂ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismIntrinsicBase.IntrinsicComparison
