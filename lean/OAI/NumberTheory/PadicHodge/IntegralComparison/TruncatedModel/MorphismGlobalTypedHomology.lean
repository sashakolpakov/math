import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomologyData

/-! # Morphism Global Typed Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology

noncomputable section

/-! Original cohomology comparisons with their exact presheaf-total types. -/
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

variable (q : ℕ)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCover.pairs p k n u
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁
local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂
local notation "M₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.sourceGlobal p k n I₁
local notation "M₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCone.targetGlobal p k n I₂
local notation "V₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X₁
local notation "V₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X₂
private abbrev sourcePullback : (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) :=
  GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)
private abbrev targetPullback : (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) :=
  GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
local notation "H₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology.sourcePullback p k n u
local notation "H₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology.targetPullback p k n u
private abbrev sourceBounded : ModuleCat.{2} R :=
  ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₁ n q)
private abbrev targetBounded : ModuleCat.{2} R :=
  ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₂ n q)
local notation "B₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology.sourceBounded p k n (Y₁ := Y₁) q
local notation "B₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology.targetBounded p k n (Y₂ := Y₂) q

def sourceOldComparison : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₁ K₁).total (.up ℕ)).homology q ⟶ B₁ :=
  (GlobalEdge.InjectiveCech.homologyIso p k n X₁ Y₁ f₁ I₁ q).hom

def sourceNewComparison : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U
    (((H₁).mapHomologicalComplex (.up ℕ)).obj K₁)).total (.up ℕ)).homology q ⟶ B₁ :=
  (MorphismCommonGlobal.sourceHomologyIso p k n u f₁ I₁ q).hom

def sourceGlobalComparison : (M₁).homology q ⟶ B₁ :=
  (BoundedOpen.SectionGlobal.homologyIso w₁ n I₁ q).hom

def targetOldComparison : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₂ K₂).total (.up ℕ)).homology q ⟶ B₂ :=
  (GlobalEdge.InjectiveCech.homologyIso p k n X₂ Y₂ f₂ I₂ q).hom

def targetGlobalComparison : (M₂).homology q ⟶ B₂ :=
  (BoundedOpen.SectionGlobal.homologyIso w₂ n I₂ q).hom

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_old : HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.sourceOld p k n f₁ I₁) q ≫
      sourceOldComparison p k n f₁ I₁ q = sourceGlobalComparison p k n I₁ q :=
  GlobalEdge.homology p k n X₁ Y₁ f₁ I₁ q

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_new : HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁) q ≫
      sourceNewComparison p k n u f₁ I₁ q = sourceGlobalComparison p k n I₁ q :=
  MorphismCommonGlobal.source_homology p k n u f₁ I₁ q

omit [Fintype k] [IsSeparated Y₂.hom] in
theorem target_old : HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.targetOld p k n f₂ I₂) q ≫
      targetOldComparison p k n f₂ I₂ q = targetGlobalComparison p k n I₂ q :=
  GlobalEdge.homology p k n X₂ Y₂ f₂ I₂ q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology
