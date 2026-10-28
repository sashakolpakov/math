import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrameReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily

/-! # Witt Frame Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameReduction

noncomputable section

/-! The fixed global Witt frame family commutes with canonical prime-power reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

def morphism (i : StandardCover.Index k X) : (WittFrameFamily.Family.frame p k X n i).obj ⟶ (WittFrameFamily.Family.frame p k X m i).obj :=
  Open.SmoothWittFrameReduction.morphism p k (WittFrameFamily.Family.liftRing p k X i) (StandardCover.coordinateRing k X i)
    (WittFrameFamily.Family.reduction p k X i) (WittFrameFamily.Family.reduction_surjective p k X i) (WittFrameFamily.Family.reduction_kernel p k X i)
    (WittFrameFamily.Family.reduction_base p k X i) X (StandardCover.chartMap k X i) (StandardCover.chartMap_over k X i) n m hnm

def iso (i : StandardCover.Index k X) : WittFrameFamily.Family.frame p k X n i ≅
    (Crystalline.LevelReductionFunctor.functor n).obj (WittFrameFamily.Family.frame p k X m i).obj :=
  Open.SmoothWittFrameReduction.boundedIso p k (WittFrameFamily.Family.liftRing p k X i) (StandardCover.coordinateRing k X i)
    (WittFrameFamily.Family.reduction p k X i) (WittFrameFamily.Family.reduction_surjective p k X i) (WittFrameFamily.Family.reduction_kernel p k X i)
    (WittFrameFamily.Family.reduction_base p k X i) X (StandardCover.chartMap k X i) (StandardCover.chartMap_over k X i) n m hnm

theorem iso_hom (i : StandardCover.Index k X) : (iso p k X n m hnm i).hom.hom ≫
    Crystalline.LevelReduction.hom n (WittFrameFamily.Family.frame p k X m i).obj = morphism p k X n m hnm i :=
  Open.SmoothWittFrameReduction.iso_hom p k (WittFrameFamily.Family.liftRing p k X i) (StandardCover.coordinateRing k X i)
    (WittFrameFamily.Family.reduction p k X i) (WittFrameFamily.Family.reduction_surjective p k X i) (WittFrameFamily.Family.reduction_kernel p k X i)
    (WittFrameFamily.Family.reduction_base p k X i) X (StandardCover.chartMap k X i) (StandardCover.chartMap_over k X i) n m hnm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameReduction
