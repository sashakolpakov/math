import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinementCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafNaturalityCoordinates

/-! # Morphism Frame Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement.Comparison

noncomputable section

/-! Refinement of the original frame-to-injective comparison, on cochains and cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem homology_square {C : Type*} [Category C] [Abelian C]
    {K L M N : CochainComplex C ℕ}
    {a : K ⟶ L} {b : L ⟶ N} {c : K ⟶ M} {d : M ⟶ N}
    (h : a ≫ b = c ≫ d) (q : ℕ) :
    HomologicalComplex.homologyMap a q ≫ HomologicalComplex.homologyMap b q =
      HomologicalComplex.homologyMap c q ≫ HomologicalComplex.homologyMap d q :=
  (HomologicalComplex.homologyMap_comp a b q).symm.trans
    ((congrArg (fun e => HomologicalComplex.homologyMap e q) h).trans
      (HomologicalComplex.homologyMap_comp c d q))

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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)

abbrev source_cochain :=
  MorphismPresheafNaturalityCoordinates.source.{1, 2} p k n u R
    (FrameInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)
    (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
    (MorphismFrameRefinementCoordinates.Comparison.source_coordinates p k n u f₁ hp₁ I₁)

abbrev target_cochain :=
  MorphismPresheafNaturalityCoordinates.target.{1, 2} p k n u R
    (FrameInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂)
    (MorphismFrameInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂)
    (MorphismFrameRefinementCoordinates.Comparison.target_coordinates p k n u f₂ hp₂ I₂)

abbrev source (q : ℕ) := homology_square (source_cochain p k n u f₁ hp₁ I₁) q

abbrev target (q : ℕ) := homology_square (target_cochain p k n u f₂ hp₂ I₂) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement.Comparison
