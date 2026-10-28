import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameInjectiveHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismCommonGlobal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare

/-! # Morphism Frame Cech Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameCechHomology

noncomputable section

/-! Actual model pullbacks commute with the native frame-to-injective comparison on common-cover Cech cohomology in every degree. -/

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
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def sourceComparison := AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1, 2} R E
  (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
def targetComparison := AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1, 2} R E
  (MorphismFrameInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂)
def sourceMap := AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map.{1, 2} R E
  (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq)
def targetMap := MorphismCommonGlobal.geometricMap p k n u v f₁ f₂ sq I₁ I₂

abbrev homology (q : ℕ) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalHomotopySquare.CechTotalHomotopySquare.homology.{1, 2} R E
    (MorphismFrameInjectiveHomotopy.targetComparison p k n u f₂ hp₂ I₂)
    (MorphismSectionHomotopy.injectiveMap p k n u v f₁ f₂ sq I₁ I₂)
    (MorphismFrameDiagonal.map p k n u v f₁ f₂ hp₁ hp₂ sq)
    (MorphismFrameInjectiveHomotopy.sourceComparison p k n u f₁ hp₁ I₁)
    (MorphismFrameInjectiveHomotopy.homotopy p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameCechHomology
