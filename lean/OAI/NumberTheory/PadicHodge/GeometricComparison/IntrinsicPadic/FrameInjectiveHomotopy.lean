import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagonal
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyPrecomposition

/-! # Frame Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy

noncomputable section

/-! The original native frame-to-injective comparison is geometrically
natural up to homotopy on compatible affine pairs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

def sourceComparison := FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.sourceMap p u f₁ hp₁ n ≫
  DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁
def targetComparison := FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.targetMap p u f₂ hp₂ n ≫
  DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂

omit [IsProper X₂.hom] [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_coordinates_component (q : ℕ) (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (((((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.sourcePullback p u).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁)).f q).app U) =
      ((sourceComparison p u f₁ hp₁ n I₁).f q).app U := rfl

omit [IsProper X₁.hom] [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_coordinates_component (q : ℕ) (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (((((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetPullback p u).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂)).f q).app U) =
      ((targetComparison p u f₂ hp₂ n I₂).f q).app U := rfl

def homotopy : Homotopy
    (targetComparison p u f₂ hp₂ n I₂ ≫ SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.map p u v f₁ f₂ hp₁ hp₂ hsquare n ≫ sourceComparison p u f₁ hp₁ n I₁) :=
  HomotopyPrecomposition.HomotopyPrecompositionSquare.homotopy
    (FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.targetMap p u f₂ hp₂ n)
    (FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.sourceMap p u f₁ hp₁ n)
    (DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy.targetComparison p u f₂ hp₂ n I₂)
    (DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy.sourceComparison p u f₁ hp₁ n I₁)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.map p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (DiagonalCech.IntrinsicPadicGeometricDiagonalCech.diagonalMap p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy.homotopy p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)
    (FrameDiagonal.IntrinsicPadicGeometricFrameDiagonal.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameInjectiveHomotopy.IntrinsicPadicGeometricFrameInjectiveHomotopy
