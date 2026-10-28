import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalSourceCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology

/-! # Morphism Global Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology

noncomputable section

/-! Refinement and the actual geometric map on injective Cech cohomology identify the original bounded crystalline pullback in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

variable (q : ℕ)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "e₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.edge p k n X₁ Y₁ f₁ I₁) q
local notation "e₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.edge p k n X₂ Y₂ f₂ I₂) q
local notation "r₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.sourceMap p k n u f₁ I₁) q
local notation "r₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.targetMap p k n u f₂ I₂) q
local notation "p₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.sourceEdge p k n u f₁ I₁) q
local notation "p₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.targetEdge p k n u f₂ I₂) q
local notation "a" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.globalMap p k n v I₁ I₂) q
local notation "b" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂) q
local notation "g" => ModuleCat.ofHom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n q)
local notation "i₁" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech.homologyIso p k n X₁ Y₁ f₁ I₁ q)
local notation "i₂" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech.homologyIso p k n X₂ Y₂ f₂ I₂ q)
local notation "h" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ q)
local notation "j₁" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₁ n I₁ q)
local notation "j₂" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₂ n I₂ q)
attribute [local instance] MorphismGlobalCohomologyData.sourceEdgeEpi MorphismGlobalCohomologyData.targetEdgeEpi MorphismGlobalSourceCohomology.sourceTypedEdgeEpi MorphismGlobalSourceCohomology.targetTypedEdgeEpi

abbrev target :=
  MorphismPresheafCoordinates.Comparison.target p k n u
    (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂)
    (MorphismGlobalCone.targetGlobal p k n I₂)
    (MorphismGlobalTypedEdges.targetCone p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetOld p k n f₂ I₂)
    (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂)
    (MorphismGlobalTypedEdges.target_old p k n f₂ I₂)
    (MorphismGlobalTypedEdges.target_new p k n u f₂ I₂)
    q _ _ _ _
    (GlobalTypedGeometricHomology.Morphism.global p k n v I₁ I₂ q)
    (HomologicalComplex.homologyMap
      (MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁) q)
    (GlobalTypedGeometricHomology.Morphism.geometric p k n u v f₁ f₂ sq I₁ I₂ q)
    (MorphismGlobalTypedHomology.sourceNewComparison p k n u f₁ I₁ q)
    (GlobalTypedGeometricHomology.Morphism.pullback p k n v q)
    (MorphismGlobalTypedHomology.targetOldComparison p k n f₂ I₂ q)
    (MorphismGlobalTypedHomology.sourceGlobalComparison p k n I₁ q)
    (MorphismGlobalTypedHomology.targetGlobalComparison p k n I₂ q)
    (GlobalTypedGeometricHomology.Morphism.edge p k n u v f₁ f₂ sq I₁ I₂ q)
    (MorphismGlobalTypedHomology.source_new p k n u f₁ I₁ q)
    (GlobalTypedGeometricHomology.Morphism.comparison p k n v I₁ I₂ q)
    (MorphismGlobalTypedHomology.target_old p k n f₂ I₂ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology
