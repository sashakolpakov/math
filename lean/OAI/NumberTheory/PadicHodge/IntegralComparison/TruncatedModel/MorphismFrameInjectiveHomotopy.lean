import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameDiagonal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition

/-! # Morphism Frame Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameInjectiveHomotopy

noncomputable section

/-! The original native frame-to-injective comparison is geometrically
natural up to homotopy on compatible affine pairs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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

def sourceComparison := MorphismFrameDiagonal.sourceMap p k n u f₁ hp₁ ≫
  MorphismDiagonalInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁
def targetComparison := MorphismFrameDiagonal.targetMap p k n u f₂ hp₂ ≫
  MorphismDiagonalInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂

omit [IsProper X₂.hom] [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_coordinates_component (q : ℕ) (U : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    (((((MorphismDiagonalRefinement.sourcePullback p k n u).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)).f q).app U) =
      ((sourceComparison p k n u f₁ hp₁ I₁).f q).app U := rfl

omit [IsProper X₁.hom] [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_coordinates_component (q : ℕ) (U : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    (((((MorphismDiagonalRefinement.targetPullback p k n u).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂)).f q).app U) =
      ((targetComparison p k n u f₂ hp₂ I₂).f q).app U := rfl

def homotopy : Homotopy
    (targetComparison p k n u f₂ hp₂ I₂ ≫ MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq ≫ sourceComparison p k n u f₁ hp₁ I₁) :=
  GeometricComparison.HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy
    (MorphismFrameDiagonal.targetMap p k n u f₂ hp₂)
    (MorphismFrameDiagonal.sourceMap p k n u f₁ hp₁)
    (MorphismDiagonalInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂)
    (MorphismDiagonalInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismDiagonalCech.diagonalMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismDiagonalInjectiveHomotopy.homotopy p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂)
    (MorphismFrameDiagonal.natural p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameInjectiveHomotopy
