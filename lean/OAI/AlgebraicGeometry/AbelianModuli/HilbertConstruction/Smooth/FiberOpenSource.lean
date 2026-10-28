import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Fiber Open Source -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberOpenSource

noncomputable section

/-! Smooth fibers remain smooth after restriction to an open subscheme of the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem smooth_fiber_precomp_open
    {X Y S : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) [IsOpenImmersion j]
    (s : S) [Smooth (f.fiberToSpecResidueField s)] : Smooth ((j ≫ f).fiberToSpecResidueField s) := by
  have : Smooth (pullback.snd f (S.fromSpecResidueField s)) :=
    inferInstanceAs (Smooth (f.fiberToSpecResidueField s))
  have hj : Smooth j := SmoothOfRelativeDimension.smooth 0 j
  have : Smooth (pullback.snd j (pullback.fst f (S.fromSpecResidueField s))) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback j (pullback.fst f (S.fromSpecResidueField s))) hj
  have : Smooth (pullbackRightPullbackFstIso f (S.fromSpecResidueField s) j).inv := inferInstance
  have : Smooth (pullback.snd j (pullback.fst f (S.fromSpecResidueField s)) ≫
      pullback.snd f (S.fromSpecResidueField s)) := AlgebraicGeometry.smooth_comp _ _
  have hh : Smooth ((pullbackRightPullbackFstIso f (S.fromSpecResidueField s) j).inv ≫
      pullback.snd j (pullback.fst f (S.fromSpecResidueField s)) ≫
      pullback.snd f (S.fromSpecResidueField s)) := AlgebraicGeometry.smooth_comp _ _
  exact (congrArg Smooth (pullbackRightPullbackFstIso_inv_snd_snd f (S.fromSpecResidueField s) j)).mp hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FiberOpenSource
