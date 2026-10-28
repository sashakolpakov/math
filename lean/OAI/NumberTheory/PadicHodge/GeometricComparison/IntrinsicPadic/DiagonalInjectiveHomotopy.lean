import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinedNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyRefined
import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafComplex

/-! # Diagonal Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy

noncomputable section

/-! The original native diagonal-to-injective comparisons commute
with arbitrary actual geometric pullback up to cochain homotopy. -/

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

local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n
local notation "S'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n
local notation "r₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.sourceMap p u f₁ hp₁ n
local notation "r₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetMap p u f₂ hp₂ n
local notation "d" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalCech.IntrinsicPadicGeometricDiagonalCech.diagonalMap p u v f₁ f₂ hp₁ hp₂ hsquare n
local notation "c₁" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₁ Y₁ f₁ hp₁ n I₁
local notation "c₂" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X₂ Y₂ f₂ hp₂ n I₂

def sourceComparison := r₁ ≫ ((S').mapHomologicalComplex (.up ℕ)).map c₁
def targetComparison := r₂ ≫ ((S).mapHomologicalComplex (.up ℕ)).map c₂

omit [IsProper X₂.hom] [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_coordinates_component (q : ℕ) (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (((((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.sourcePullback p u).mapHomologicalComplex (.up ℕ)).map
      (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X₁ Y₁ f₁ hp₁ n I₁)).f q).app U) =
      ((sourceComparison p u f₁ hp₁ n I₁).f q).app U := rfl

omit [IsProper X₁.hom] [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_coordinates_component (q : ℕ) (U : (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ) :
    (((((DiagonalRefinement.IntrinsicPadicGeometricDiagonalRefinement.targetPullback p u).mapHomologicalComplex (.up ℕ)).map
      (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.map p X₂ Y₂ f₂ hp₂ n I₂)).f q).app U) =
      ((targetComparison p u f₂ hp₂ n I₂).f q).app U := rfl

def homotopy : Homotopy
    (targetComparison p u f₂ hp₂ n I₂ ≫ SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (d ≫ sourceComparison p u f₁ hp₁ n I₁) :=
  HomotopyRefined.HomotopyRefinedSquare.homotopy r₂ r₁ d
    (((S).mapHomologicalComplex (.up ℕ)).map c₂) (((S').mapHomologicalComplex (.up ℕ)).map c₁)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.injectiveMap p u v f₁ f₂ hsquare n I₁ I₂)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.targetMap p u v f₁ f₂ hp₁ hp₂ hsquare n)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.sourceMap p u f₁ hp₁ n)
    (((S').mapHomologicalComplex (.up ℕ)).map (InjectiveHomotopy.IntrinsicPadicGeometricInjectiveHomotopy.comparison p u f₁ hp₁ n I₁))
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.target p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)
    (SectionHomotopy.IntrinsicPadicGeometricSectionHomotopy.source p u f₁ hp₁ n I₁)
    (DiagonalRefinedNaturality.IntrinsicPadicGeometricDiagonalRefinedNaturality.natural p u v f₁ f₂ hp₁ hp₂ hsquare n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveHomotopy.IntrinsicPadicGeometricDiagonalInjectiveHomotopy
