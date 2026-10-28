import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafFrameGlobalTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology

/-! # Morphism Source Homology Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomologyCoordinates.Raw

noncomputable section

section

/-! The native bounded crystalline frame comparison commutes with
actual model pullback through its original common affine cover. -/

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

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

omit [Fintype k] [IsSeparated Y₁.hom] in
theorem source_new : HomologicalComplex.homologyMap
      (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁) q ≫
        MorphismSourceHomology.Raw.comparison p k n u f₁ I₁ q =
      MorphismGlobalTypedHomology.sourceGlobalComparison p k n I₁ q :=
  MorphismGlobalTypedHomology.source_new p k n u f₁ I₁ q

end

/-! The native bounded crystalline frame comparison commutes with
actual model pullback through its original common affine cover. -/

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

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

def geometric :
    ((GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex (MorphismCover.pairs p k n u)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
        (A := ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
        (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj
          (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂))).total (.up ℕ)).homology q ⟶
      (MorphismSourceHomology.Raw.complex p k n u f₁ I₁).homology q :=
  GlobalTypedGeometricHomology.Morphism.geometric p k n u v f₁ f₂ sq I₁ I₂ q

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem geometric_edge : HomologicalComplex.homologyMap
    (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂) q ≫
    geometric p k n u v f₁ f₂ sq I₁ I₂ q =
    GlobalTypedGeometricHomology.Morphism.global p k n v I₁ I₂ q ≫
      HomologicalComplex.homologyMap
        (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁) q :=
  GlobalTypedGeometricHomology.Morphism.edge p k n u v f₁ f₂ sq I₁ I₂ q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomologyCoordinates.Raw
