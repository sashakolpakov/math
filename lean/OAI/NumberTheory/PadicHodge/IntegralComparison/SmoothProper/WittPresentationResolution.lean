import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology

/-! # Witt Presentation Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationResolution

noncomputable section

/-! The constructed finite flat Witt frame cover gives a genuine resolution of the original crystalline constant source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "site" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n

def complex : ChainComplex (Sheaf site (ModuleCat.{u + 1} R)) ℕ :=
  CoveringPresentationResolution.complex.{u + 1, u} site R (WittFrameFamily.Family.frame p k X n)

def augmentation : complex p k X n ⟶ (ChainComplex.single₀ _).obj
    (BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n) :=
  CoveringPresentationResolution.augmentation.{u + 1, u} site R (WittFrameFamily.Family.frame p k X n)

theorem augmentation_quasiIso : QuasiIso (augmentation p k X n) :=
  CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u} site R (WittFrameFamily.Family.frame p k X n)
    (WittFrameCover.covering p k X n)

def degreeZeroIso : (complex p k X n).homology 0 ≅
    BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n :=
  CoveringPresentationResolution.degreeZeroIso.{u + 1, u} site R (WittFrameFamily.Family.frame p k X n)
    (WittFrameCover.covering p k X n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationResolution
