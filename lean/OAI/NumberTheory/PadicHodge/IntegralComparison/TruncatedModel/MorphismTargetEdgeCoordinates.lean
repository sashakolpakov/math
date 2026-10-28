import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetConeCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.GlobalTypedGeometricHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TotalTypedGlobalEdge

/-! # Morphism Target Edge Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetEdgeCoordinates

noncomputable section

/-! The original target edge square with its native homology-map types. -/
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

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem global_coordinate (q : ℕ) :
    GlobalTypedGeometricHomology.Morphism.global p k n v I₁ I₂ q =
      HomologicalComplex.homologyMap
        (MorphismGlobalCone.globalMap p k n v I₁ I₂) q := rfl

attribute [local irreducible] GlobalTypedGeometricHomology.Morphism.global

abbrev edgeData :=
  Cech.TotalTypedGlobalEdge.Cone.homology.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (MorphismCover.pairs p k n u)
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

abbrev edge (q : ℕ) := edgeGlobal p k n u v f₁ f₂ sq I₁ I₂ q
  (global_coordinate p k n v I₁ I₂ q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetEdgeCoordinates
