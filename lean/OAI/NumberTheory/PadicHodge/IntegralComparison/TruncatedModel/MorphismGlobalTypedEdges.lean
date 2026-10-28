import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementSteps

/-! # Morphism Global Typed Edges -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedEdges

noncomputable section

/-! Native cone and edge maps with their exact presheaf-total types cached explicitly. -/
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

local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁
local notation "M₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.sourceGlobal p k n I₁
local notation "V₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X₁
private abbrev sourcePullback : (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) :=
  GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback F₁
local notation "H₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedEdges.sourcePullback p k n u

def sourceCone : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₁.left.affineOpens)).obj M₁ ⟶ K₁ :=
  GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₁ n I₁ S₁

def sourceOld : M₁ ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₁ K₁).total (.up ℕ) :=
  GlobalEdge.edge p k n X₁ Y₁ f₁ I₁

def sourceNew : M₁ ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U
    (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₁).mapHomologicalComplex (.up ℕ)).obj K₁)).total (.up ℕ) :=
  MorphismCommonGlobal.sourceEdge p k n u f₁ I₁

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_old : sourceOld p k n f₁ I₁ =
    GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map V₁ K₁ M₁ (sourceCone p k n f₁ I₁) :=
  MorphismGlobalRefinementSteps.Whole.source_old p k n f₁ I₁

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_new : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
    (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₁).mapHomologicalComplex (.up ℕ)).obj K₁) M₁
    (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₁ K₁ M₁ (sourceCone p k n f₁ I₁)) =
      sourceNew p k n u f₁ I₁ :=
  MorphismGlobalRefinementSteps.Whole.source_new p k n u f₁ I₁

local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂
local notation "M₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.targetGlobal p k n I₂
local notation "V₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X₂
private abbrev targetPullback : (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) :=
  GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback F₂
local notation "H₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedEdges.targetPullback p k n u

def targetCone : (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := X₂.left.affineOpens)).obj M₂ ⟶ K₂ :=
  GeometricComparison.Bounded.SectionConeRefinement.BoundedSectionConeRefinement.oldCone w₂ n I₂ S₂

def targetOld : M₂ ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₂ K₂).total (.up ℕ) :=
  GlobalEdge.edge p k n X₂ Y₂ f₂ I₂

def targetNew : M₂ ⟶ (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U
    (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₂).mapHomologicalComplex (.up ℕ)).obj K₂)).total (.up ℕ) :=
  MorphismCommonGlobal.targetEdge p k n u f₂ I₂

omit [Fintype k] [IsSeparated Y₂.hom] in
theorem target_old : targetOld p k n f₂ I₂ =
    GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map V₂ K₂ M₂ (targetCone p k n f₂ I₂) :=
  MorphismGlobalRefinementSteps.Whole.target_old p k n f₂ I₂

omit [Fintype k] [IsSeparated Y₂.hom] in
theorem target_new : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map U
    (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R) F₂).mapHomologicalComplex (.up ℕ)).obj K₂) M₂
    (GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone F₂ K₂ M₂ (targetCone p k n f₂ I₂)) =
      targetNew p k n u f₂ I₂ :=
  MorphismGlobalRefinementSteps.Whole.target_new p k n u f₂ I₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedEdges
