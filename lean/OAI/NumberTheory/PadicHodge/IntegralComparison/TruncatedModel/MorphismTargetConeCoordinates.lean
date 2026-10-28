import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetGeometricEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalEdgeCoordinates

/-! # Morphism Target Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetConeCoordinates

noncomputable section

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

abbrev sections :=
  (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj
      (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂))

def cone :
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)).obj
      (MorphismGlobalCone.targetGlobal p k n I₂) ⟶
    sections p k n u f₂ I₂ :=
  GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)
    (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂)
    (MorphismGlobalCone.targetGlobal p k n I₂)
    (MorphismGlobalTypedEdges.targetCone p k n f₂ I₂)

omit [Fintype k] [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem naturality : cone p k n u f₂ I₂ ≫
    MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂ =
    (GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant (C := AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)).map
      (MorphismGlobalCone.globalMap p k n v I₁ I₂) ≫
        MorphismGlobalCone.sourceCone p k n u f₁ I₁ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext V
  exact MorphismGlobalCone.component p k n u v f₁ f₂ sq I₁ I₂ q V

abbrev edgeData :=
  Cech.ConeTotalEdgeCoordinates.homology.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (MorphismCover.pairs p k n u)
    (cone p k n u f₂ I₂)
    (MorphismGlobalCone.sourceCone p k n u f₁ I₁)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismGlobalCone.globalMap p k n v I₁ I₂)
    (naturality p k n u v f₁ f₂ sq I₁ I₂)

abbrev edgeMaps := edgeData p k n u v f₁ f₂ sq I₁ I₂
  (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂)
  (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁)

abbrev edgeCoordinates := edgeMaps p k n u v f₁ f₂ sq I₁ I₂
  (MorphismGlobalTypedEdges.target_new p k n u f₂ I₂).symm rfl

abbrev edge (q : ℕ) := edgeCoordinates p k n u v f₁ f₂ sq I₁ I₂ q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetConeCoordinates
