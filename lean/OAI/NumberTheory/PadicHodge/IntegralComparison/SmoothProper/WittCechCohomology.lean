import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafCohomology

/-! # Witt Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCohomology

noncomputable section

/-! The constructed finite Witt frame family computes original global bounded cohomology through its actual ring Čech complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  BoundedFrame.CechPresheafCohomology.complex p k (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n)

def homologyIso (i : ℕ) : (complex p k X n).homology i ≅ ModuleCat.of R
    (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) :=
  BoundedFrame.CechPresheafCohomology.homologyIso p k (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n)
    (WittFrameCover.covering p k X n) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCohomology
