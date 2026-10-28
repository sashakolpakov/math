import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetEdgeCoordinates

/-! # Morphism Target Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetEdge

noncomputable section

/-! The exact edge proposition consumed by the native target comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HomologicalComplex.homology

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

attribute [local irreducible] GlobalTypedGeometricHomology.Morphism.global

abbrev edgeData :=
  Cech.TotalTypedGlobalEdge.Cone.homology.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (MorphismCover.pairs p k n u)
    (K := (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj
          (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂)))
    (L := MorphismCommonGlobal.sourceSections p k n u f₁ I₁)
    (M := MorphismGlobalCone.targetGlobal p k n I₂)
    (N := MorphismGlobalCone.sourceGlobal p k n I₁)
    (MorphismTargetConeCoordinates.cone p k n u f₂ I₂)
    (MorphismGlobalCone.sourceCone p k n u f₁ I₁)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismGlobalCone.globalMap p k n v I₁ I₂)
    (MorphismTargetConeCoordinates.naturality p k n u v f₁ f₂ sq I₁ I₂)

abbrev edgeMaps := edgeData p k n u v f₁ f₂ sq I₁ I₂
  (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂)
  (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁)

abbrev edgeCoordinates := edgeMaps p k n u v f₁ f₂ sq I₁ I₂
  (MorphismGlobalTypedEdges.target_new p k n u f₂ I₂).symm rfl

abbrev edgeGlobal (q : ℕ) := edgeCoordinates p k n u v f₁ f₂ sq I₁ I₂ q
  (GlobalTypedGeometricHomology.Morphism.global p k n v I₁ I₂ q)

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem edge (q : ℕ) :
    HomologicalComplex.homologyMap
      (MorphismGlobalTypedEdges.targetNew p k n u f₂ I₂) q ≫
      HomologicalComplex.homologyMap
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
          (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
          (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
          (K := (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafRefined.CechPresheafRefinedCohomology.pullback.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left)).mapHomologicalComplex (.up ℕ)).obj
          (MorphismGlobalRefinementBase.Maps.targetSections p k n f₂ I₂)))
          (L := MorphismCommonGlobal.sourceSections p k n u f₁ I₁)
          (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)) q =
    GlobalTypedGeometricHomology.Morphism.global p k n v I₁ I₂ q ≫
      HomologicalComplex.homologyMap
        (MorphismCommonGlobal.sourceEdge p k n u f₁ I₁) q :=
  edgeGlobal p k n u v f₁ f₂ sq I₁ I₂ q
    (MorphismTargetEdgeCoordinates.global_coordinate p k n v I₁ I₂ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetEdge
