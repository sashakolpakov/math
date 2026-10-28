import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.StandardEtaleLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SmoothWittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameFlatness

/-! # Witt Frame Family -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

noncomputable section

/-! A fixed finite family of constructed Witt lifts gives flat frames at every original crystalline level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

abbrev liftRing (i : StandardCover.Index k X) :=
  Witt.StandardEtaleLift.Ring p k (StandardCover.coordinateIndex k X i) (StandardCover.coordinateRing k X i) (StandardCover.presentation k X i)

def reduction (i : StandardCover.Index k X) : liftRing p k X i →+* StandardCover.coordinateRing k X i :=
  Witt.StandardEtaleLift.reduction p k (StandardCover.coordinateIndex k X i) (StandardCover.coordinateRing k X i) (StandardCover.presentation k X i)

omit [Fintype k] [CharP k p] in
theorem reduction_surjective (i : StandardCover.Index k X) : Function.Surjective (reduction p k X i) :=
  Witt.StandardEtaleLift.reduction_surjective p k (StandardCover.coordinateIndex k X i)
    (StandardCover.coordinateRing k X i) (StandardCover.presentation k X i)

theorem reduction_kernel (i : StandardCover.Index k X) : RingHom.ker (reduction p k X i) =
    Ideal.span {(p : liftRing p k X i)} :=
  Witt.StandardEtaleLift.reduction_kernel p k (StandardCover.coordinateIndex k X i)
    (StandardCover.coordinateRing k X i) (StandardCover.presentation k X i)

omit [Fintype k] [CharP k p] in
theorem reduction_base (i : StandardCover.Index k X) (w : WittVector p k) :
    reduction p k X i (algebraMap (WittVector p k) (liftRing p k X i) w) =
      algebraMap k (StandardCover.coordinateRing k X i) (WittVector.constantCoeff w) :=
  Witt.StandardEtaleLift.reduction_base p k (StandardCover.coordinateIndex k X i)
    (StandardCover.coordinateRing k X i) (StandardCover.presentation k X i) w

def frame (n : ℕ) (i : StandardCover.Index k X) : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n :=
  Open.SmoothWittFrame.boundedFrame p k (liftRing p k X i) (StandardCover.coordinateRing k X i)
    (reduction p k X i) (reduction_surjective p k X i) (reduction_kernel p k X i)
    (reduction_base p k X i) X (StandardCover.chartMap k X i) (StandardCover.chartMap_over k X i) n

def coefficientBase (n : ℕ) (i : StandardCover.Index k X) :
    (WittVector p k ⧸ (Ideal.span {(p : WittVector p k)}) ^ (n + 1)) →+* (frame p k X n i).obj.ring :=
  SmoothWitt.FrameFlatness.base p k (liftRing p k X i) n

theorem coefficientBase_mk (n : ℕ) (i : StandardCover.Index k X) (w : WittVector p k) :
    coefficientBase p k X n i
      (Ideal.Quotient.mk ((Ideal.span {(p : WittVector p k)}) ^ (n + 1)) w) =
        (frame p k X n i).obj.base w := rfl

theorem flat (n : ℕ) (i : StandardCover.Index k X) : (coefficientBase p k X n i).Flat :=
  SmoothWitt.FrameFlatness.flat p k (liftRing p k X i) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family
