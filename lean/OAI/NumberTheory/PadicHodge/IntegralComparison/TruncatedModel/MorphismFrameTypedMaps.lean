import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedInferred
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafTypedRefinement

/-! # Morphism Frame Typed Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedMaps.Homology

noncomputable section

/-! The native bounded crystalline comparison factors through the
common affine cover, compatibly with actual geometric pullback. -/

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
local notation "V₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X₁
local notation "V₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X₂
local notation "K₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.sourceSections p k n f₁ I₁
local notation "K₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂
local notation "C₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁)
local notation "C₂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) (OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap.source p k n X₂ Y₂ f₂ hp₂)
private abbrev sourcePullback : (X₁.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) :=
  GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left)
private abbrev targetPullback : (X₂.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} R) :=
  GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
local notation "H₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedMaps.Homology.sourcePullback p k n u
local notation "H₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedMaps.Homology.targetPullback p k n u

abbrev sourceFrameOld : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₁ C₁).total (.up ℕ)
abbrev targetFrameOld : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₂ C₂).total (.up ℕ)
abbrev sourceFrameNew : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (((H₁).mapHomologicalComplex (.up ℕ)).obj C₁)).total (.up ℕ)
abbrev targetFrameNew : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (((H₂).mapHomologicalComplex (.up ℕ)).obj C₂)).total (.up ℕ)
abbrev sourceInjectiveOld : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₁ K₁).total (.up ℕ)
abbrev targetInjectiveOld : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V₂ K₂).total (.up ℕ)
abbrev sourceInjectiveNew : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (((H₁).mapHomologicalComplex (.up ℕ)).obj K₁)).total (.up ℕ)
abbrev targetInjectiveNew : CochainComplex (ModuleCat.{2} R) ℕ :=
  (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (((H₂).mapHomologicalComplex (.up ℕ)).obj K₂)).total (.up ℕ)

def sourceOldMap : (sourceFrameOld p k n f₁ hp₁) ⟶
    (sourceInjectiveOld p k n f₁ I₁) :=
  FrameCech.Comparison.map p k n X₁ Y₁ f₁ hp₁ I₁

def targetOldMap : (targetFrameOld p k n f₂ hp₂) ⟶
    (targetInjectiveOld p k n f₂ I₂) :=
  FrameCech.Comparison.map p k n X₂ Y₂ f₂ hp₂ I₂

def sourceNewMap : (sourceFrameNew p k n u f₁ hp₁) ⟶
    (sourceInjectiveNew p k n u f₁ I₁) :=
  MorphismFrameCechHomology.sourceComparison p k n u f₁ hp₁ I₁

def targetNewMap : (targetFrameNew p k n u f₂ hp₂) ⟶
    (targetInjectiveNew p k n u f₂ I₂) :=
  MorphismFrameCechHomology.targetComparison p k n u f₂ hp₂ I₂

def sourceFrameRefinementMap : (sourceFrameOld p k n f₁ hp₁) ⟶
    (sourceFrameNew p k n u f₁ hp₁) :=
  MorphismFrameRefinementCoordinates.Comparison.sourceFrameRefinement p k n u f₁ hp₁

def targetFrameRefinementMap : (targetFrameOld p k n f₂ hp₂) ⟶
    (targetFrameNew p k n u f₂ hp₂) :=
  MorphismFrameRefinementCoordinates.Comparison.targetFrameRefinement p k n u f₂ hp₂

def sourceInjectiveRefinementMap : (sourceInjectiveOld p k n f₁ I₁) ⟶
    (sourceInjectiveNew p k n u f₁ I₁) :=
  MorphismPresheafTypedRefinement.sourceMap p k n u K₁

def targetInjectiveRefinementMap : (targetInjectiveOld p k n f₂ I₂) ⟶
    (targetInjectiveNew p k n u f₂ I₂) :=
  MorphismPresheafTypedRefinement.targetMap p k n u K₂

def geometricMap : (targetFrameNew p k n u f₂ hp₂) ⟶
    (sourceFrameNew p k n u f₁ hp₁) :=
  MorphismFrameCechHomology.sourceMap p k n u v f₁ f₂ hp₁ hp₂ sq

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameTypedMaps.Homology
