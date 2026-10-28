import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceHomologyCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalMapCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPresheafFrameGlobalTarget
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGlobalCohomology

/-! # Morphism Target Geometric Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetGeometricEdge

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

variable (q : ℕ)
attribute [local instance] MorphismGlobalSourceCohomology.targetTypedEdgeEpi

private theorem homology_square {C : Type*} [Category C] [Abelian C]
    {K L M N : CochainComplex C ℕ}
    {a : K ⟶ L} {b : L ⟶ N} {c : K ⟶ M} {d : M ⟶ N}
    (h : a ≫ b = c ≫ d) (i : ℕ) :
    HomologicalComplex.homologyMap a i ≫ HomologicalComplex.homologyMap b i =
      HomologicalComplex.homologyMap c i ≫ HomologicalComplex.homologyMap d i :=
  (HomologicalComplex.homologyMap_comp a b i).symm.trans
    ((congrArg (fun e => HomologicalComplex.homologyMap e i) h).trans
      (HomologicalComplex.homologyMap_comp c d i))

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem totalMap_eq :
    MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂ =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
        (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂) :=
  Cech.ConeTotalMapCoordinates.map.{1,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (MorphismCover.pairs p k n u)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)

omit [Fintype k] [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem cochain_edge :
    MorphismCommonGlobal.targetEdge p k n u f₂ I₂ ≫
      AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1,2}
        (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
        (NonemptyCechNerve.nerve (MorphismCover.pairs p k n u))
        (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂) =
    MorphismGlobalCone.globalMap p k n v I₁ I₂ ≫
      MorphismCommonGlobal.sourceEdge p k n u f₁ I₁ :=
  (congrArg (fun a =>
    MorphismCommonGlobal.targetEdge p k n u f₂ I₂ ≫ a)
      (totalMap_eq p k n u v f₁ f₂ sq I₁ I₂)).symm.trans
        (MorphismCommonGlobal.naturality p k n u v f₁ f₂ sq I₁ I₂)

abbrev edge :=
  homology_square (cochain_edge p k n u v f₁ f₂ sq I₁ I₂) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTargetGeometricEdge
