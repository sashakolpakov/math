import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.DiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalTransportAugmentation

/-! # Cech Sheaf Augmentation Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafAugmentationCoordinates

noncomputable section

/-! The actual global ramified model resolution and comparison preserve bounded-level restriction and their original augmentations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "baseMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) baseMap n
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) baseMap n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.diagram p k n X Y f hp
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.cone p k n X Y f hp

local instance separated : IsSeparated baseMap := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) baseMap n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := W))
    (BoundedCrystalline.Site.topology baseMap n)

theorem cone_eq : GeometricComparison.CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.cone S P
    (Bounded.RelativeSheafComplex.structureIso baseMap n) η =
      ResolutionDiagram.augmentation p k n X Y f hp := by
  apply NatTrans.ext
  funext U
  exact GeometricComparison.CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.cone_app S P
    (Bounded.RelativeSheafComplex.structureIso baseMap n) η U

variable [IsProper X.hom] [X.left.IsSeparated]

theorem augmentation : CechSheafResolution.augmentation p k n X Y f hp ≫
    (DiagonalCech.Comparison.totalIso p k n X Y f hp).hom =
      GeometricComparison.CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.opens p k n X)
        (ResolutionDiagram.diagram p k n X Y f hp)
        ((CochainComplex.single₀ _).obj O) (ResolutionDiagram.augmentation p k n X Y f hp) :=
  (GeometricComparison.CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.augmentation S (CechSliceResolution.opens p k n X) P
    (Bounded.RelativeSheafComplex.structureIso baseMap n) η).trans
      (congrArg (fun η' => GeometricComparison.CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.opens p k n X)
        (ResolutionDiagram.diagram p k n X Y f hp) ((CochainComplex.single₀ _).obj O) η')
        (cone_eq p k n X Y f hp))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafAugmentationCoordinates
