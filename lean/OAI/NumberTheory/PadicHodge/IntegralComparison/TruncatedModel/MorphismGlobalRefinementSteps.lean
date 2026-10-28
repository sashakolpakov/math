import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.SectionRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafEdge

/-! # Morphism Global Refinement Steps -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementSteps

/-! The original model global edges refine to the actual common-cover edges as cochain maps. -/

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

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_old (q : ℕ) :
    (GlobalEdge.edge p k n X₁ Y₁ f₁ I₁).f q =
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldRawEdge w₁ n I₁ S₁
      (CechSliceResolution.opens p k n X₁)).f q :=
  (MorphismGlobalRefinementCoordinates.source_old_component p k n f₁ I₁ q).trans
    (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.old_edge_component w₁ n I₁ S₁
      (CechSliceResolution.opens p k n X₁) q)

omit [IsSeparated Y₁.hom] in
omit [Fintype k] in
theorem source_middle (q : ℕ) :
    (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldRawEdge w₁ n I₁ S₁
      (CechSliceResolution.opens p k n X₁)).f q ≫
      (MorphismGlobalRefinementBase.Maps.sourceMap p k n u f₁ I₁).f q =
        (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₁).mapHomologicalComplex (.up ℕ)).obj (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁))
      (MorphismGlobalCone.sourceGlobal p k n I₁) (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₁ (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁) (MorphismGlobalCone.sourceGlobal p k n I₁)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₁ n I₁ S₁))).f q :=
  MorphismPresheafEdge.source_native_component p k n u
    (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁) (MorphismGlobalCone.sourceGlobal p k n I₁)
    (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₁ n I₁ S₁) q

omit [Fintype k] [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₁.hom] in
theorem source_new_cone (q : ℕ) (Z : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    ((GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₁ (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁) (MorphismGlobalCone.sourceGlobal p k n I₁)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₁ n I₁ S₁)).f q).app Z =
      ((MorphismGlobalCone.sourceCone p k n u f₁ I₁).f q).app Z := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_new (q : ℕ) :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₁).mapHomologicalComplex (.up ℕ)).obj (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁))
      (MorphismGlobalCone.sourceGlobal p k n I₁) (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₁ (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁) (MorphismGlobalCone.sourceGlobal p k n I₁)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₁ n I₁ S₁))).f q =
      (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁).f q :=
  GeometricComparison.CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr.component U (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₁).mapHomologicalComplex (.up ℕ)).obj (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁))
    (MorphismGlobalCone.sourceGlobal p k n I₁) (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₁ (MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁) (MorphismGlobalCone.sourceGlobal p k n I₁)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₁ n I₁ S₁))
    (MorphismGlobalCone.sourceCone p k n u f₁ I₁) q
    (source_new_cone p k n u f₁ I₁ q)

omit [Fintype k] [IsSeparated Y₂.hom] in
theorem target_old (q : ℕ) :
    (GlobalEdge.edge p k n X₂ Y₂ f₂ I₂).f q =
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldRawEdge w₂ n I₂ S₂
      (CechSliceResolution.opens p k n X₂)).f q :=
  (MorphismGlobalRefinementCoordinates.target_old_component p k n f₂ I₂ q).trans
    (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.old_edge_component w₂ n I₂ S₂
      (CechSliceResolution.opens p k n X₂) q)

omit [IsSeparated Y₂.hom] in
omit [Fintype k] in
theorem target_middle (q : ℕ) :
    (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldRawEdge w₂ n I₂ S₂
      (CechSliceResolution.opens p k n X₂)).f q ≫
      (MorphismGlobalRefinementBase.Maps.targetMap p k n u f₂ I₂).f q =
        (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₂).mapHomologicalComplex (.up ℕ)).obj (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂))
      (MorphismGlobalCone.targetGlobal p k n I₂) (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₂ (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂) (MorphismGlobalCone.targetGlobal p k n I₂)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₂ n I₂ S₂))).f q :=
  MorphismPresheafEdge.target_native_component p k n u
    (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂) (MorphismGlobalCone.targetGlobal p k n I₂)
    (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₂ n I₂ S₂) q

omit [Fintype k] [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₂.hom] in
theorem target_new_cone (q : ℕ) (Z : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ) :
    ((GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₂ (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂) (MorphismGlobalCone.targetGlobal p k n I₂)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₂ n I₂ S₂)).f q).app Z =
      ((MorphismGlobalCone.targetCone p k n u f₂ I₂).f q).app Z := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

omit [Fintype k] [IsSeparated Y₂.hom] in
theorem target_new (q : ℕ) :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₂).mapHomologicalComplex (.up ℕ)).obj (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂))
      (MorphismGlobalCone.targetGlobal p k n I₂) (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₂ (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂) (MorphismGlobalCone.targetGlobal p k n I₂)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₂ n I₂ S₂))).f q =
      (MorphismCommonGlobal.targetEdge p k n u f₂ I₂).f q :=
  GeometricComparison.CechPresheaf.ConeComponentCongr.CechPresheafConeComponentCongr.component U (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₂).mapHomologicalComplex (.up ℕ)).obj (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂))
    (MorphismGlobalCone.targetGlobal p k n I₂) (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₂ (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂) (MorphismGlobalCone.targetGlobal p k n I₂)
      (GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₂ n I₂ S₂))
    (MorphismGlobalCone.targetCone p k n u f₂ I₂) q
    (target_new_cone p k n u f₂ I₂ q)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementSteps

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementSteps.Whole

/-! Original global-edge refinement assembled before taking any total-complex component. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem eq_of_components {C : Type*} [Category C] [HasZeroMorphisms C]
    {K L : CochainComplex C ℕ} {a b : K ⟶ L}
    (h : ∀ q, a.f q = b.f q) : a = b := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact h q

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

abbrev source_old := eq_of_components
  (MorphismGlobalRefinementSteps.source_old p k n f₁ I₁)

abbrev source_new := eq_of_components
  (MorphismGlobalRefinementSteps.source_new p k n u f₁ I₁)

abbrev target_old := eq_of_components
  (MorphismGlobalRefinementSteps.target_old p k n f₂ I₂)

abbrev target_new := eq_of_components
  (MorphismGlobalRefinementSteps.target_new p k n u f₂ I₂)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementSteps.Whole

end

end OAI
