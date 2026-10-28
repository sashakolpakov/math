import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomologyData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafCoordinates

/-! # Morphism Global Source Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalSourceCohomology

noncomputable section

/-! Refinement and the actual geometric map on injective Cech cohomology identify the original bounded crystalline pullback in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cancel_after_edge {C : Type*} [Category* C]
    {G K P B : C} {edge : G ⟶ K} {refinement : K ⟶ P}
    {comparison : P ⟶ B} {identification : K ⟶ B} [Epi edge]
    (hc : (edge ≫ refinement) ≫ comparison = edge ≫ identification) :
    refinement ≫ comparison = identification :=
  (cancel_epi edge).1 ((Category.assoc edge refinement comparison).symm.trans hc)

private theorem postcomp_equality {C : Type*} [Category* C]
    {A B D : C} {a b : A ⟶ B} (h : a = b) (c : B ⟶ D) :
    a ≫ c = b ≫ c := congrArg (fun m => m ≫ c) h

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
local notation "e₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁) q
local notation "e₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.edge p k n X₂ Y₂ f₂ I₂) q
local notation "r₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafRefinement.sourceMap p k n u (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁)) q
local notation "r₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.targetMap p k n u f₂ I₂) q
local notation "p₁" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁) q
local notation "p₂" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.targetEdge p k n u f₂ I₂) q
local notation "a" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.globalMap p k n v I₁ I₂) q
local notation "b" => HomologicalComplex.homologyMap (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂) q
local notation "g" => ModuleCat.ofHom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames.ambient_over p k v) n q)
local notation "i₁" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech.homologyIso p k n X₁ Y₁ f₁ I₁ q)
local notation "i₂" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge.InjectiveCech.homologyIso p k n X₂ Y₂ f₂ I₂ q)
local notation "h" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ q)
local notation "j₁" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₁ n I₁ q)
local notation "j₂" => Iso.hom (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₂ n I₂ q)
attribute [local instance] MorphismGlobalCohomologyData.sourceEdgeEpi MorphismGlobalCohomologyData.targetEdgeEpi

local instance sourceTypedEdgeEpi : Epi (HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁) q) :=
  MorphismGlobalCohomologyData.sourceEdgeEpi p k n f₁ I₁ q

local instance targetTypedEdgeEpi : Epi (HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.targetOld p k n f₂ I₂) q) :=
  MorphismGlobalCohomologyData.targetEdgeEpi p k n f₂ I₂ q

omit [Fintype k] [IsSeparated Y₁.hom] in
private theorem sourceRefinementCoordinates : p₁ = e₁ ≫ r₁ :=
  ((HomologicalComplex.homologyMap_comp
    (MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁)
    (MorphismPresheafRefinement.sourceMap p k n u
      (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁)) q).symm.trans
    (congrArg (fun edgeMap => HomologicalComplex.homologyMap edgeMap q)
      (MorphismGlobalWholeRefinement.source_edge p k n u f₁ I₁))).symm

omit [Fintype k] [IsSeparated Y₁.hom] in
private theorem sourceCommonCoordinates : p₁ ≫ h = j₁ :=
  MorphismCommonGlobal.source_homology p k n u f₁ I₁ q

omit [Fintype k] [IsSeparated Y₁.hom] in
private theorem sourceOriginalCoordinates : e₁ ≫ i₁ = j₁ :=
  GlobalEdge.homology p k n X₁ Y₁ f₁ I₁ q

private abbrev source_refined_edge :=
  postcomp_equality (sourceRefinementCoordinates p k n u f₁ I₁ q).symm h

private abbrev source_direct_edge :=
  (sourceCommonCoordinates p k n u f₁ I₁ q).trans
    (sourceOriginalCoordinates p k n f₁ I₁ q).symm

private abbrev source_after_edge :=
  (source_refined_edge p k n u f₁ I₁ q).trans (source_direct_edge p k n u f₁ I₁ q)

abbrev source := cancel_after_edge (source_after_edge p k n u f₁ I₁ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalSourceCohomology
