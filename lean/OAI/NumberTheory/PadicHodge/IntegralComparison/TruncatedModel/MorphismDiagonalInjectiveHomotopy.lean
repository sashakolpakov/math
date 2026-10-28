import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinedNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.HomotopyRefined
import OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafComplex

/-! # Morphism Diagonal Injective Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalInjectiveHomotopy

noncomputable section

/-! The original native diagonal-to-injective comparisons commute
with arbitrary actual geometric pullback up to cochain homotopy. -/

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

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.targetSections p k n u f₂
local notation "S'" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap.sourceSections p k n u f₁
local notation "r₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinement.sourceMap p k n u f₁ hp₁
local notation "r₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalRefinement.targetMap p k n u f₂ hp₂
local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalCech.diagonalMap p k n u v f₁ f₂ hp₁ hp₂ sq
local notation "c₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁
local notation "c₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂

def sourceComparison := r₁ ≫ ((S').mapHomologicalComplex (.up ℕ)).map c₁
def targetComparison := r₂ ≫ ((S).mapHomologicalComplex (.up ℕ)).map c₂

omit [IsProper X₂.hom] [Smooth X₂.hom] [IsSeparated Y₂.hom] in
theorem source_coordinates_component (q : ℕ) (U : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    (((((MorphismDiagonalRefinement.sourcePullback p k n u).mapHomologicalComplex (.up ℕ)).map
      (DiagonalCech.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)).f q).app U) =
      ((sourceComparison p k n u f₁ hp₁ I₁).f q).app U := rfl

omit [IsProper X₁.hom] [Smooth X₁.hom] [IsSeparated Y₁.hom] in
theorem target_coordinates_component (q : ℕ) (U : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    (((((MorphismDiagonalRefinement.targetPullback p k n u).mapHomologicalComplex (.up ℕ)).map
      (DiagonalCech.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂)).f q).app U) =
      ((targetComparison p k n u f₂ hp₂ I₂).f q).app U := rfl

def homotopy : Homotopy
    (targetComparison p k n u f₂ hp₂ I₂ ≫ MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (d ≫ sourceComparison p k n u f₁ hp₁ I₁) :=
  GeometricComparison.HomotopyRefined.HomotopyRefinedSquare.homotopy r₂ r₁ d
    (((S).mapHomologicalComplex (.up ℕ)).map c₂) (((S').mapHomologicalComplex (.up ℕ)).map c₁)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismSectionHomotopy.targetMap p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismSectionHomotopy.sourceMap p k n u f₁ hp₁)
    (((S').mapHomologicalComplex (.up ℕ)).map (MorphismInjectiveHomotopy.comparison p k n u f₁ hp₁ I₁))
    (MorphismSectionHomotopy.target p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂)
    (MorphismSectionHomotopy.source p k n u f₁ hp₁ I₁)
    (MorphismDiagonalRefinedNaturality.natural p k n u v f₁ f₂ hp₁ hp₂ sq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagonalInjectiveHomotopy
