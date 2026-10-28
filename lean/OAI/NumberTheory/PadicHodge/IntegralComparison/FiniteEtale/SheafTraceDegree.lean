import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.DeRhamSheafTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.TraceDegree

/-! # Sheaf Trace Degree -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SheafTraceDegree.DeRham

noncomputable section

/-! The native finite étale trace composed with pullback is the
coefficient degree on the full original sheaf de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.TraceDegree.DeRham

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]

local instance degreeCoordinateOrder (i : TraceBasis.Index R X Y f) :
    LinearOrder (TraceBasis.coordinateIndex R X Y f i) := TraceBasis.coordinateOrder R X Y f i

variable (d : ℕ) (hd : ∀ i : TraceBasis.Index R X Y f,
  Algebra.trace (AffineOpen.DeRhamTrace.targetRing R Y (TraceBasis.opens R X Y f i))
    (AffineOpen.DeRhamTrace.sourceRing R X Y f (TraceBasis.opens R X Y f i)) 1 = (d : AffineOpen.DeRhamTrace.targetRing R Y (TraceBasis.opens R X Y f i)))

include hd in
theorem pullback_trace_of_degree :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f ≫ DeRhamSheafTrace.trace R X Y f =
      d • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X n).obj
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X n) (TraceBasis.isBasis R X Y f)
  intro i
  change ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f).f n).hom.app (op (TraceBasis.opens R X Y f i)) ≫
      ((DeRhamSheafTrace.trace R X Y f).f n).hom.app (op (TraceBasis.opens R X Y f i)) = d • 𝟙 _
  rw [DeRhamSheafTrace.trace_app]
  have h := AffineOpen.TraceDegree.DeRham.pullback_trace_of_degree R X Y f (TraceBasis.opens R X Y f i)
    (TraceBasis.coordinateIndex R X Y f i)
    (Module.Free.chooseBasis (AffineOpen.DeRhamTrace.targetRing R Y (TraceBasis.opens R X Y f i))
      (AffineOpen.DeRhamTrace.sourceRing R X Y f (TraceBasis.opens R X Y f i))) d (hd i)
  exact congrArg (fun t => t.f n) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SheafTraceDegree.DeRham
