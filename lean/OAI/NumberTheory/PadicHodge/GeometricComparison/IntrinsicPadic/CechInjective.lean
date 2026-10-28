import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives
import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedInjective

/-! # Cech Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison

noncomputable section

/-! The actual native global Čech resolution compares to every injective
resolution of the original bounded crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n

local notation "h" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation_quasiIso p X Y f hp n

variable (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def map :=
  AugmentedInjective.AugmentedInjectiveComparison.map K a h I

theorem augmentation : a ≫ IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I = I.ι :=
  AugmentedInjective.AugmentedInjectiveComparison.augmentation K a h I

theorem map_quasiIso : QuasiIso (IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I) :=
  AugmentedInjective.AugmentedInjectiveComparison.quasiIso K a h I

def homotopy (b : K ⟶ I.cocomplex) (hb : a ≫ b = I.ι) : Homotopy (IntrinsicPadicCechInjectiveComparison.map p X Y f hp n I) b :=
  AugmentedInjective.AugmentedInjectiveComparison.homotopy K a h I b hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison
