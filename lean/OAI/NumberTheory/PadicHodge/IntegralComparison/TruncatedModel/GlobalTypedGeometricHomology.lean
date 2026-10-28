import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalTypedHomology

/-! # Global Typed Geometric Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology.Morphism

noncomputable section

/-! The original geometric cohomology maps with exact common-cover types. -/
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
local notation "H₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology.Morphism.sourcePullback p k n u
local notation "H₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology.Morphism.targetPullback p k n u
private abbrev sourceBounded : ModuleCat.{2} R :=
  ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₁ n q)
private abbrev targetBounded : ModuleCat.{2} R :=
  ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w₂ n q)
local notation "B₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology.Morphism.sourceBounded p k n (Y₁ := Y₁) q
local notation "B₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology.Morphism.targetBounded p k n (Y₂ := Y₂) q

def geometric : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U
    (((H₂).mapHomologicalComplex (.up ℕ)).obj K₂)).total (.up ℕ)).homology q ⟶
    ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U
    (((H₁).mapHomologicalComplex (.up ℕ)).obj K₁)).total (.up ℕ)).homology q :=
  HomologicalComplex.homologyMap
    (MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂) q

def global : (M₂).homology q ⟶ (M₁).homology q :=
  HomologicalComplex.homologyMap
    (MorphismGlobalCone.globalMap p k n v I₁ I₂) q

def pullback :=
  letI : Ring R := (inferInstance : CommRing R).toRing
  ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) v.left
    (MorphismData.Frames.ambient_over p k v) n q)

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem edge : HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂) q ≫
      geometric p k n u v f₁ f₂ sq I₁ I₂ q =
    global p k n v I₁ I₂ q ≫ HomologicalComplex.homologyMap
      (MorphismGlobalTypedEdges.sourceNew p k n u f₁ I₁) q :=
  MorphismGlobalCohomologyData.geometric_edge p k n u v f₁ f₂ sq I₁ I₂ q

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem comparison : global p k n v I₁ I₂ q ≫
      MorphismGlobalTypedHomology.sourceGlobalComparison p k n I₁ q =
    MorphismGlobalTypedHomology.targetGlobalComparison p k n I₂ q ≫
      pullback p k n v q :=
  GeometricComparison.Bounded.OpenCohomology.BoundedGeometricOpenCohomology.homology v.left
    (MorphismData.Frames.ambient_over p k v) n I₂ I₁ q

local instance coefficientRing : Ring R := (inferInstance : CommRing R).toRing

private abbrev domainOf {C : Type*} [Category* C] {X Y : C} (_f : X ⟶ Y) : C := X
private abbrev codomainOf {C : Type*} [Category* C] {X Y : C} (_f : X ⟶ Y) : C := Y

-- Check the bounded output conversions before inserting these maps into a frame comparison.
def targetOldAtPullback : ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₂ K₂).total (.up ℕ)).homology q ⟶
    domainOf (pullback p k n v q) :=
  MorphismGlobalTypedHomology.targetOldComparison p k n f₂ I₂ q

def sourceGlobalAtPullback : (M₁).homology q ⟶ codomainOf (pullback p k n v q) :=
  MorphismGlobalTypedHomology.sourceGlobalComparison p k n I₁ q

def targetGlobalAtPullback : (M₂).homology q ⟶ domainOf (pullback p k n v q) :=
  MorphismGlobalTypedHomology.targetGlobalComparison p k n I₂ q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology.Morphism
