import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameTransitionComposition

/-! # Witt Frame Transition Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameTransitionComposition

noncomputable section

/-! The fixed global Witt frame reductions are compatible at every level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family
  WittFrameReduction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

theorem identity (n : ℕ) (i : StandardCover.Index k X) : WittFrameReduction.morphism p k X n n le_rfl i = 𝟙 _ := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  exact congrArg DFunLike.coe (PD.TruncationTransition.map_refl (WittFrameFamily.Family.liftRing p k X i)
    (Ideal.span {(p : WittFrameFamily.Family.liftRing p k X i)}) n)

theorem composition (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) (i : StandardCover.Index k X) :
    WittFrameReduction.morphism p k X n m hnm i ≫ WittFrameReduction.morphism p k X m l hml i = WittFrameReduction.morphism p k X n l (hnm.trans hml) i := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DividedPowers.DPMorphism.ext
  exact congrArg DFunLike.coe (PD.TruncationTransition.map_comp (WittFrameFamily.Family.liftRing p k X i)
    (Ideal.span {(p : WittFrameFamily.Family.liftRing p k X i)}) n m hnm l hml)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameTransitionComposition
