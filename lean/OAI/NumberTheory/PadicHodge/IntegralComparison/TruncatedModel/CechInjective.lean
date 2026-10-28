import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedInjective

/-! # Cech Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechInjective.Comparison

noncomputable section

/-! The actual native global Čech resolution compares to every injective
resolution of the original bounded crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) w n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution.complex p k n X Y f hp
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution.augmentation p k n X Y f hp

local notation "h" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution.augmentation_quasiIso p k n X Y f hp

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k Y) n))

def map :=
  GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison.map K a h I

theorem augmentation : a ≫ Comparison.map p k n X Y f hp I = I.ι :=
  GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison.augmentation K a h I

theorem map_quasiIso : QuasiIso (Comparison.map p k n X Y f hp I) :=
  GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison.quasiIso K a h I

def homotopy (b : K ⟶ I.cocomplex) (hb : a ≫ b = I.ι) : Homotopy (Comparison.map p k n X Y f hp I) b :=
  GeometricComparison.AugmentedInjective.AugmentedInjectiveComparison.homotopy K a h I b hb

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechInjective.Comparison
