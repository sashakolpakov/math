import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicDiagonalCechComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalTransportAugmentation

/-! # Cech Sheaf Augmentation Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates

noncomputable section

/-! The original native sheafified Cech augmentation is the canonical
augmentation of the actual sheaf-resolution diagram under its total isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.cone p X Y f hp n

local instance separated : IsSeparated wittMap := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance sheafCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W))
    (IntegralComparison.BoundedCrystalline.Site.topology wittMap n)

theorem cone_eq : CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.cone S P
    (IntegralComparison.Bounded.RelativeSheafComplex.structureIso wittMap n) η =
      PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp n := by
  apply NatTrans.ext
  funext U
  exact CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.cone_app S P
    (IntegralComparison.Bounded.RelativeSheafComplex.structureIso wittMap n) η U

variable [IsProper X.hom] [X.left.IsSeparated]

theorem augmentation : CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n ≫
    (PadicDiagonalCechComparison.IntrinsicPadicDiagonalCechComparison.totalIso p X Y f hp n).hom =
      CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
        (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n)
        ((CochainComplex.single₀ _).obj O) (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp n) :=
  (CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.augmentation S (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X) P
    (IntegralComparison.Bounded.RelativeSheafComplex.structureIso wittMap n) η).trans
      (congrArg (fun η' => CechCone.Total.CechConeTotal.augmentation (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
        (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n) ((CochainComplex.single₀ _).obj O) η')
        (cone_eq p X Y f hp n))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates
