import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafAugmentationCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.MappedInjective

/-! # Incoming -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Incoming.Comparison

noncomputable section

/-! The native local comparison on a fixed special-fiber open
preserves the original augmentation and is unique up to homotopy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.augmentation p k n X Y f hp
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction.restriction p k n X Y f V
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingRestriction.meet_isIso p k n X Y f hp V

local instance globalSeparated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance restriction_additive : (R).Additive := by
  dsimp only [IncomingRestriction.restriction]
  infer_instance
local instance restriction_limits : PreservesFiniteLimits R := by
  dsimp only [IncomingRestriction.restriction]
  infer_instance
local instance restriction_colimits : PreservesFiniteColimits R := by
  dsimp only [IncomingRestriction.restriction]
  infer_instance
local instance restriction_injectives : (R).PreservesInjectiveObjects := by
  dsimp only [IncomingRestriction.restriction]
  infer_instance

local instance globalCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := W))
    (BoundedCrystalline.Site.topology w n)
local instance localCoproducts : HasCoproducts.{0}
    (BoundedOpen.Subsite.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
      w (f ⁻¹ᵁ V.val).ι n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := W))
    (BoundedOpen.Subsite.topology w (f ⁻¹ᵁ V.val).ι n)

abbrev augmentation := GeometricComparison.Semilattice.MappedInjective.SemilatticeMappedInjectiveComparison.augmentation X.left.affineOpens V R P η

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev map := GeometricComparison.Semilattice.MappedInjective.SemilatticeMappedInjectiveComparison.map X.left.affineOpens U V R P H
  (DiagonalCech.Comparison.totalIso p k n X Y f hp) J
  (CechInjective.Comparison.map p k n X Y f hp J)

abbrev augmentation_map := GeometricComparison.Semilattice.MappedInjective.SemilatticeMappedInjectiveComparison.augmentation_map
  X.left.affineOpens U V R P H η
  (DiagonalCech.Comparison.totalIso p k n X Y f hp)
  (CechSheafResolution.augmentation p k n X Y f hp)
  (CechSheafAugmentationCoordinates.augmentation p k n X Y f hp) J
  (CechInjective.Comparison.map p k n X Y f hp J)
  (CechInjective.Comparison.augmentation p k n X Y f hp J)

variable (i : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hi : V.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (Truncated.Witt.Ring p k n) X i)

include hi in
theorem augmentation_quasiIso : QuasiIso (augmentation p k n X Y f hp V) := by
  let := IncomingRestriction.augmentation_quasiIso p k n X Y f hp V i hi
  exact GeometricComparison.Semilattice.MappedInjective.SemilatticeMappedInjectiveComparison.augmentation_quasiIso X.left.affineOpens V R P η

def homotopy
    (c : ((R).mapHomologicalComplex (.up ℕ)).obj ((P).obj (op V)) ⟶
      (ExactInjectiveResolution.map R J).cocomplex)
    (hc : augmentation p k n X Y f hp V ≫ c = (ExactInjectiveResolution.map R J).ι) :
    Homotopy (Comparison.map p k n X Y f hp V J) c := by
  let := augmentation_quasiIso p k n X Y f hp V i hi
  exact Augmented.ResolutionHomotopy.homotopy _ (augmentation p k n X Y f hp V)
    (ExactInjectiveResolution.map R J) _ c
    ((augmentation_map p k n X Y f hp V J).trans hc.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Incoming.Comparison
