import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCup

/-! # Smooth Proper Witt Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SmoothProperWittCup

noncomputable section

/-! The augmentation-normalized balanced product on original bounded
crystalline cohomology, using the genuine smooth proper Witt frame cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev resolutionHomologyIso (n i : ℕ) :=
  BalancedBounded.CechCup.resolutionHomologyIso p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n) i

abbrev homologyIso (n i : ℕ) :=
  BalancedBounded.CechCup.presheafHomologyIso p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n) i

abbrev equivalence (n i : ℕ) :=
  BalancedBounded.CechCup.cohomologyEquiv p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n) i

abbrev cup (n i j : ℕ) :=
  BalancedBounded.CechCup.cup p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n) i j

abbrev cup_comparison (n i j : ℕ) :=
  BalancedBounded.CechCup.cup_comparison p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n) i j

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SmoothProperWittCup
