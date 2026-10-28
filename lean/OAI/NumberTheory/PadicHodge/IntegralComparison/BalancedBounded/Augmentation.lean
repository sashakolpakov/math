import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.IntrinsicFrameAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.PresheafCup

/-! # Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.Augmentation

noncomputable section

/-! The augmentation-normalized comparison on the original bounded
crystalline groups, in the literal ambient-ring Čech coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup.resolution p k f n
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex.presheafComplex f n F

variable (K : CochainComplex (Sheaf (BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n)
    (ModuleCat.{u+1} (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))) ℕ)
  (a : (CochainComplex.single₀ _).obj
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) ⟶ K)
  (g : K ⟶ (CechCup.resolution p k f n).cocomplex)
  (ha : a ≫ g = (CechCup.resolution p k f n).ι)

abbrev comparison (i : ℕ) :=
  Balanced.IntrinsicFrameAugmentation.Intrinsic.comparison.{u+1,u,u+2} F CR (BoundedCrystalline.Site.topology f n)
    hcover I K g i

def map : C ⟶ (FrameCech.IntrinsicTotalCoordinates.Intrinsic.bicomplex.{u+1,u} F CR (BoundedCrystalline.Site.topology f n) K).total (.up ℕ) :=
  (BoundedFrame.CechComplex.presheafIso f n F).hom ≫
    FrameCech.IntrinsicTotalCoordinates.Intrinsic.edge.{u+1,u} F CR (BoundedCrystalline.Site.topology f n) K a

include ha in
theorem augmentation (i : ℕ) (x : (C).homology i) :
    comparison p k f n F hcover K g i (HomologicalComplex.homologyMap (map p k f n F K a) i x) =
      PresheafCup.equivalence p k f n F hcover i x := by
  dsimp only [map]
  erw [HomologicalComplex.homologyMap_comp]
  change comparison p k f n F hcover K g i
    (HomologicalComplex.homologyMap
      (FrameCech.IntrinsicTotalCoordinates.Intrinsic.edge.{u+1,u} F CR (BoundedCrystalline.Site.topology f n) K a) i
      (HomologicalComplex.homologyMap (BoundedFrame.CechComplex.presheafIso f n F).hom i x)) = _
  erw [Balanced.IntrinsicFrameAugmentation.Intrinsic.augmentation.{u+1,u,u+2} F CR (BoundedCrystalline.Site.topology f n)
    hcover I (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n F) K a g ha]
  erw [← Lifted.HomologyCoordinates.naturality.{u+1,u+1,u+2} CR
    (BoundedFrame.CechComplex.presheafIso f n F).hom i x]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.Augmentation
