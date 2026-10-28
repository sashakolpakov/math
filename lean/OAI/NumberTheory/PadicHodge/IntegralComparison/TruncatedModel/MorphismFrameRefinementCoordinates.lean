import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameCechHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined

/-! # Morphism Frame Refinement Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinementCoordinates.Comparison

noncomputable section

/-! Literal native frame-refinement maps and their presheaf coordinates. -/
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

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)

def sourceFrameRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₁ U
  (CechSliceResolution.opens p k n X₁) (MorphismRefinement.source p k n u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁))
def targetFrameRefinement := GeometricComparison.CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F₂ U
  (CechSliceResolution.opens p k n X₂) (MorphismRefinement.target p k n u)
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FrameDiagonalMap.source p k n X₂ Y₂ f₂ hp₂))

omit [IsProper X₂.hom] [Smooth X₂.hom] in
theorem source_coordinates :
    (((MorphismDiagonalRefinement.sourcePullback p k n u).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁)) =
      MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext W
  exact MorphismFrameInjectiveHomotopy.source_coordinates_component p k n u f₁ hp₁ I₁ q W

omit [IsProper X₁.hom] [Smooth X₁.hom] in
theorem target_coordinates :
    (((MorphismDiagonalRefinement.targetPullback p k n u).mapHomologicalComplex (.up ℕ)).map
      (FrameInjective.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂)) =
      MorphismFrameInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext W
  exact MorphismFrameInjectiveHomotopy.target_coordinates_component p k n u f₂ hp₂ I₂ q W

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinementCoordinates.Comparison
