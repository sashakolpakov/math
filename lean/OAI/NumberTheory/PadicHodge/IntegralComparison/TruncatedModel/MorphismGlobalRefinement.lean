import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalWholeRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafEdgeHomologyCoordinates

/-! # Morphism Global Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinement

noncomputable section

/-! Common-cover refinement of the original global edges, and its action on cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u)
local notation "F₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u)
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X₁ Y₁ f₁
local notation "S₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SectionBifunctor.specialOpens p k n X₂ Y₂ f₂

abbrev source_edge :=
  MorphismGlobalWholeRefinement.source_edge p k n u f₁ I₁

abbrev target_edge :=
  MorphismGlobalWholeRefinement.target_edge p k n u f₂ I₂

abbrev source_homology (q : ℕ) :=
  PresheafEdgeHomologyCoordinates.Morphism.source_module p k n u
    (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁)
    (MorphismGlobalCone.sourceGlobal p k n I₁)
    (MorphismGlobalTypedEdges.sourceCone p k n f₁ I₁)
    (MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁)
    (MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁)
    (MorphismGlobalTypedEdges.source_old p k n f₁ I₁)
    (MorphismGlobalTypedEdges.source_new p k n u f₁ I₁) q

abbrev target_homology (q : ℕ) :=
  PresheafEdgeHomologyCoordinates.Morphism.target p k n u
    (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂)
    (MorphismGlobalCone.targetGlobal p k n I₂)
    (MorphismGlobalTypedEdges.targetCone p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetOld p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂)
    (MorphismGlobalTypedEdges.target_old p k n f₂ I₂)
    (MorphismGlobalTypedEdges.target_new p k n u f₂ I₂) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinement
